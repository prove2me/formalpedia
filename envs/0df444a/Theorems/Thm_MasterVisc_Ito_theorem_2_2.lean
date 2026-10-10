-- Prove2me | Theorems.Thm_MasterVisc_Ito_theorem_2_2
-- name    : MasterVisc.Ito.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:37:38.817106+00:00
-- url     : https://prove2.me/theorems/c715d9ac-dcce-4e8a-8574-f99c702e035a
-- title:
--   Theorem 2.2, p. 941 — the Fréchet derivative of the lift is DF(t, X̃) = ψ(X̃_{t∧·}) with ψ F̂_t-measurable, determined by f and ℙ̃_X̃
-- statement:
--   Let $(\tilde\Omega,\tilde{\mathcal F},\tilde{\mathbb P})$ be an atomless Polish probability space and let $f:\widehat\Theta\to\mathbb R$ be continuous for the pseudometric $\mathcal W_2$ of (2.5). Assume the lift $F(t,\tilde X)=f(t,\tilde{\mathbb P}_{\tilde X})$ of (2.8) is Fréchet differentiable in the sense of (2.9), with derivative $DF(t,\tilde X)\in\mathbb L^2(\tilde\Omega;\mathbb R^d)$, and that $DF$ is continuous in the sense of (2.11):
--   $$
--   \lim_{n\to\infty}\mathbb E^{\tilde{\mathbb P}}\big[|DF(t,\tilde X^n)-DF(t,\tilde X)|^2\big]=0\quad\text{whenever}\quad\lim_{n\to\infty}\mathbb E^{\tilde{\mathbb P}}\big[d^2_{SK}(\tilde X^n,\tilde X)\big]=0.
--   $$
--   Then for every $t\in[0,T]$ and $\tilde X\in\mathbb L^2(\tilde\Omega;\widehat\Omega)$ there is an $\widehat{\mathcal F}_t$-measurable $\psi:\widehat\Omega\to\mathbb R^d$ with
--   $$
--   DF(t,\tilde X)=\psi(\tilde X_{t\wedge\cdot}),\qquad\tilde{\mathbb P}\text{-a.s.}\tag{2.12}
--   $$
--   Moreover $\psi$ is determined by $f$ and $\tilde{\mathbb P}_{\tilde X}$: (2.12) holds with the same $\psi$ for every $\tilde X'\in\mathbb L^2(\tilde\Omega;\widehat\Omega)$ with $\tilde{\mathbb P}_{\tilde X'}=\tilde{\mathbb P}_{\tilde X}$; and $\psi$ is unique $\tilde{\mathbb P}_{\tilde X}$-a.s. among $\widehat{\mathcal F}_t$-measurable functions satisfying (2.12).
--
--   This is the path-dependent analogue of Lions' representation (2.2) of the derivative of a lifted function; it is what allows the paper to define $\partial_\mu f(t,\hat\mu,\hat\omega)$ by (2.16).
--
--   **Formalization Note** The atomless Polish probability space is an arbitrary Polish space with its Borel $\sigma$-algebra and a probability measure giving zero mass to every point (equivalent to atomlessness on a Polish space). The two "moreover" claims are spelled out as above; "determined by $f$ and $\tilde{\mathbb P}_{\tilde X}$" is read as "the same $\psi$ serves every $\tilde X'$ with the same law".
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), Theorem 2.2, p. 941, with (2.8)–(2.12)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_MasterVisc_Ito_Setting
import Definitions.Def_MasterVisc_Ito_Derivatives
import Definitions.Def_MasterVisc_Ito_Lift
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.Ito

theorem theorem_2_2 {d : ℕ} {T : ℝ≥0}
    {Ω' : Type} [MeasurableSpace Ω'] [TopologicalSpace Ω'] [PolishSpace Ω'] [BorelSpace Ω']
    (P : Measure Ω') [IsProbabilityMeasure P] [NullSingletonClass P]
    (f : ℝ≥0 → Measure (DPath d T) → ℝ) (hf : ContOnΘD f)
    (DF : ℝ≥0 → (Ω' → DPath d T) → Ω' → EthierKurtz.SDEState d)
    (hDF : IsFrechetLift P f DF) (hcont : IsL2ContDF P DF)
    (t : ℝ≥0) (ht : t ≤ T) (X : Ω' → DPath d T) (hX : IsL2D P X) :
    ∃ ψ : DPath d T → EthierKurtz.SDEState d,
      Measurable[FD t] ψ ∧
      (DF t X =ᵐ[P] fun ω => ψ (stopD t (X ω))) ∧
      (∀ X' : Ω' → DPath d T, IsL2D P X' → P.map X' = P.map X →
        DF t X' =ᵐ[P] fun ω => ψ (stopD t (X' ω))) ∧
      (∀ ψ' : DPath d T → EthierKurtz.SDEState d, Measurable[FD t] ψ' →
        (DF t X =ᵐ[P] fun ω => ψ' (stopD t (X ω))) → ψ' =ᵐ[P.map X] ψ) := by sorry

end MasterVisc.Ito
