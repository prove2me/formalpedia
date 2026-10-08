-- Prove2me | Theorems.Thm_LinParamBandits_UEGeneral_chernoff_infinite_arms
-- name    : LinParamBandits.UEGeneral.chernoff_infinite_arms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:23.339842+00:00
-- url     : https://prove2.me/theorems/eda54add-d416-4282-8cf3-70df6405ab0d
-- title:
--   Theorem B.2 — Chernoff inequality for uncertainty ellipsoids with infinitely many arms
-- statement:
--   Consider a run of the UE policy under Assumption 1, on an arbitrary compact set of arms. For every $t \ge r$, all $x, z \in \mathbb R^r$ and every $\zeta \ge 2$,
--   $$\Pr\Big\{x'(\widehat Z_t - z) > \zeta\kappa_0\sigma_0\sqrt{\log t}\,\|x\|_{C_t} \,\Big|\, Z = z\Big\} \le t^{r\kappa_0^2}e^{-\zeta^2/4},$$
--   and
--   $$\Pr\Big\{(U_{t+1} - x)'(\widehat Z_t - z) > \zeta\kappa_0\sigma_0\sqrt{\log t}\,\|U_{t+1} - x\|_{C_t} \,\Big|\, Z = z\Big\} \le t^{r\kappa_0^2}e^{-\zeta^2/4}.$$
--
--   Unlike Theorem B.1, the bound does not depend on the number of arms, so it applies to infinite arm sets; it is the second input of Lemma B.6.
--
--   **Formalization Note** The statement is about a run of the UE policy (`IsUE`) under Assumption 1 (`Assumption1`) on a compact nonempty arm set $\mathcal U_r \subset \mathbb R^r$, $r \ge 2$, with noise laws given by a Markov kernel $\nu$ (the law of $W^u_t$ is $\nu(u)$ for every $t$). "$\Pr\{\cdot \mid Z = z\}$" is the law `histMeasure ν z ψ t` of the history $(U_1, X_1, \dots, U_t, X_t)$ with the parameter fixed to $z$; $U_{t+1}$ is `ψ.act t h`. $C_t$ is `Cmat`, the inverse of the design matrix $\sum_{s \le t} U_s U_s'$, which is positive definite on every history that starts with $b_1, \dots, b_r$ (all histories of a UE run, since $t \ge r$). $t^{r\kappa_0^2}$ is a real power.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Theorem B.2, p. 30 (proof pp. 33–34)

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy

namespace LinParamBandits.UEGeneral

open MeasureTheory ProbabilityTheory

/-- Theorem B.2 (p. 30): Chernoff inequality for uncertainty ellipsoids with infinitely many
arms. -/
theorem chernoff_infinite_arms {r : ℕ} (hr : 2 ≤ r) {𝒰 : Set (LinParamBandits.LowerBound.Vec r)} (h𝒰c : IsCompact 𝒰) (h𝒰n : 𝒰.Nonempty)
    {ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ} [IsMarkovKernel ν] {b : Fin r → LinParamBandits.LowerBound.Vec r} {σ₀ ubar lam0 : ℝ}
    (hA : Assumption1 𝒰 ν b σ₀ ubar lam0) {ψ : Policy r} (hψ : IsUE 𝒰 b σ₀ ubar lam0 ψ)
    (t : ℕ) (ht : r ≤ t) (x z : LinParamBandits.LowerBound.Vec r) (ζ : ℝ) (hζ : 2 ≤ ζ) :
    histMeasure ν z ψ t
        {h | ζ * kappa0 ubar lam0 * σ₀ * Real.sqrt (Real.log t) * wnorm (Cmat (armsOf h)) x <
          inner ℝ x (Zhat h - z)} ≤
      ENNReal.ofReal ((t : ℝ) ^ ((r : ℝ) * kappa0 ubar lam0 ^ 2) * Real.exp (-ζ ^ 2 / 4)) ∧
    histMeasure ν z ψ t
        {h | ζ * kappa0 ubar lam0 * σ₀ * Real.sqrt (Real.log t) *
            wnorm (Cmat (armsOf h)) (ψ.act t h - x) < inner ℝ (ψ.act t h - x) (Zhat h - z)} ≤
      ENNReal.ofReal ((t : ℝ) ^ ((r : ℝ) * kappa0 ubar lam0 ^ 2) * Real.exp (-ζ ^ 2 / 4)) := by sorry

end LinParamBandits.UEGeneral
