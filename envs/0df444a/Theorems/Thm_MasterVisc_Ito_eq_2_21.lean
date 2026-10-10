-- Prove2me | Theorems.Thm_MasterVisc_Ito_eq_2_21
-- name    : MasterVisc.Ito.eq_2_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:38:03.006545+00:00
-- url     : https://prove2.me/theorems/f4b90942-ee0a-4f8b-8a96-c09b4134ae09
-- title:
--   (2.21), proof of Theorem 2.7, p. 945 — f(T, μⁿ) − f(0, μⁿ) = I₁ⁿ + I₂ⁿ + I₃ⁿ
-- statement:
--   Let $f\in C^{1,1,1}_b(\widehat\Theta)$, $L>0$, and let $\mu\in\widehat{\mathcal P}_L$ be represented as $\mu=\tilde{\mathbb P}\circ\tilde X^{-1}$. Fix $n\ge1$, the uniform partition $t_i=iT/n$, and the discretizations $\tilde X^n$, $\mu^n$, $\tilde X^{n,\theta}$, $\mu^{n,\theta}$ (on the $i$-th interval) of the proof of Theorem 2.7. Write $\Delta_i=\tilde X_{t_i,t_{i+1}}$. Then
--   $$
--   f(T,\mu^n)-f(0,\mu^n)=I_1^n+I_2^n+I_3^n,
--   $$
--   where
--   $$
--   I_1^n=\sum_{i=0}^{n-1}\int_{t_i}^{t_{i+1}}\partial_tf\big(t,\mu^n_{[0,t_i]}\big)\,dt,\qquad
--   I_2^n=\sum_{i=0}^{n-1}\int_0^1\mathbb E^{\tilde{\mathbb P}}\big[\partial_\mu f\big(t_{i+1},\mu^{n,\theta},\tilde X^n_{t_i\wedge\cdot}\big)\cdot\Delta_i\big]\,d\theta,
--   $$
--   $$
--   I_3^n=\sum_{i=0}^{n-1}\int_0^1\!\!\int_0^1\mathbb E^{\tilde{\mathbb P}}\Big[\theta\,\partial_\omega\partial_\mu f\big(t_{i+1},\mu^{n,\theta},\tilde X^{n,\tilde\theta\theta}\big):\Delta_i\Delta_i^{\top}\Big]\,d\tilde\theta\,d\theta.
--   $$
--
--   This is the discrete Itô expansion from which (2.20) follows by letting $n\to\infty$.
--
--   **Formalization Note** The page writes the proof for $d=1$ "for notational simplicity"; this is the $d$-dimensional version, in which $\partial_\mu f\,\tilde X_{t_i,t_{i+1}}$ is the inner product and $\theta|\tilde X_{t_i,t_{i+1}}|^2\,\partial_\omega\partial_\mu f$ is $\theta\,\partial_\omega\partial_\mu f:\Delta_i\Delta_i^\top$. Only the first and last lines of the display are stated; the intermediate equalities are steps of the proof.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), proof of Theorem 2.7, (2.21), p. 945

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_MasterVisc_Ito_Setting
import Definitions.Def_MasterVisc_Ito_Derivatives
import Definitions.Def_MasterVisc_Ito_Discretization
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.Ito

theorem eq_2_21 {d : ℕ} {T : ℝ≥0} (Φ : C111DataD d T) (hΦ : IsC111bD Φ)
    (L : ℝ) (hL : 0 < L) (μ : Measure (DPath d T)) (R : Rep d T) (hR : InPLhat L μ R)
    (n : ℕ) (hn : 1 ≤ n) :
    Φ.fn T (lawStep R n) - Φ.fn 0 (lawStep R n) =
      (∑ i ∈ Finset.range n, ∫ s in (grid T n i : ℝ)..(grid T n (i + 1) : ℝ),
          Φ.dt s.toNNReal ((lawStep R n).map (stopD (grid T n i))))
      + (∑ i ∈ Finset.range n, ∫ θ in (0 : ℝ)..1, ∫ ω,
          inner ℝ (Φ.dmu (grid T n (i + 1)) (lawTheta R n i θ)
              (stopD (grid T n i) (stepD n (R.Y ω))))
            (incr n i (R.Y ω)) ∂(R.P))
      + (∑ i ∈ Finset.range n, ∫ θ in (0 : ℝ)..1, ∫ θ' in (0 : ℝ)..1, ∫ ω,
          θ * MasterVisc.Comparison.fdot (Φ.dwdmu (grid T n (i + 1)) (lawTheta R n i θ) (thetaD n i (θ' * θ) (R.Y ω)))
            (Matrix.of fun a b => incr n i (R.Y ω) a * incr n i (R.Y ω) b) ∂(R.P)) := by sorry

end MasterVisc.Ito
