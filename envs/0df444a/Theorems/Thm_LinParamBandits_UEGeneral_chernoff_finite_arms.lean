-- Prove2me | Theorems.Thm_LinParamBandits_UEGeneral_chernoff_finite_arms
-- name    : LinParamBandits.UEGeneral.chernoff_finite_arms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:03.028774+00:00
-- url     : https://prove2.me/theorems/462dd307-2fa1-4775-973d-ac510cde5c2e
-- title:
--   Theorem B.1 — Chernoff inequality for uncertainty ellipsoids with finitely many arms
-- statement:
--   Consider a run of the UE policy under Assumption 1, and suppose the set of arms $\mathcal U_r$ is finite, with $|\mathcal U_r|$ elements. Then for every $t \ge r$, all $x, z \in \mathbb R^r$ and every $\zeta > 0$,
--   $$\Pr\Big\{x'(\widehat Z_t - z) > \zeta\sigma_0\|x\|_{C_t} \,\Big|\, Z = z\Big\} \le t^{5|\mathcal U_r|}e^{-\zeta^2/2},$$
--   and
--   $$\Pr\Big\{(U_{t+1} - x)'(\widehat Z_t - z) > \zeta\sigma_0\|U_{t+1} - x\|_{C_t} \,\Big|\, Z = z\Big\} \le t^{5|\mathcal U_r|}e^{-\zeta^2/2}.$$
--
--   This extends the Chernoff inequality to least squares estimates built from adaptively chosen arms; together with Theorem B.2 it controls the uncertainty radius in Lemma B.6.
--
--   **Formalization Note** The statement is about a run of the UE policy (`IsUE`) under Assumption 1 (`Assumption1`) on a compact nonempty arm set $\mathcal U_r \subset \mathbb R^r$, $r \ge 2$, with noise laws given by a Markov kernel $\nu$ (the law of $W^u_t$ is $\nu(u)$ for every $t$). "$\Pr\{\cdot \mid Z = z\}$" is the law `histMeasure ν z ψ t` of the history $(U_1, X_1, \dots, U_t, X_t)$ with the parameter fixed to $z$; $U_{t+1}$ is `ψ.act t h`. $C_t$ is `Cmat`, the inverse of the design matrix $\sum_{s \le t} U_s U_s'$, which is positive definite on every history that starts with $b_1, \dots, b_r$ (all histories of a UE run, since $t \ge r$). The paper states the result "under Assumption 1"; finiteness of $\mathcal U_r$ is the hypothesis of the theorem's title (p. 30: for infinitely many arms the bound is vacuous).
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Theorem B.1, p. 29

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy

namespace LinParamBandits.UEGeneral

open MeasureTheory ProbabilityTheory

/-- Theorem B.1 (p. 29): Chernoff inequality for uncertainty ellipsoids with finitely many arms. -/
theorem chernoff_finite_arms {r : ℕ} (hr : 2 ≤ r) {𝒰 : Set (LinParamBandits.LowerBound.Vec r)} (h𝒰c : IsCompact 𝒰) (h𝒰n : 𝒰.Nonempty)
    {ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ} [IsMarkovKernel ν] {b : Fin r → LinParamBandits.LowerBound.Vec r} {σ₀ ubar lam0 : ℝ}
    (hA : Assumption1 𝒰 ν b σ₀ ubar lam0) {ψ : Policy r} (hψ : IsUE 𝒰 b σ₀ ubar lam0 ψ)
    (hfin : 𝒰.Finite) (t : ℕ) (ht : r ≤ t) (x z : LinParamBandits.LowerBound.Vec r) (ζ : ℝ) (hζ : 0 < ζ) :
    histMeasure ν z ψ t
        {h | ζ * σ₀ * wnorm (Cmat (armsOf h)) x < inner ℝ x (Zhat h - z)} ≤
      ENNReal.ofReal ((t : ℝ) ^ (5 * 𝒰.ncard) * Real.exp (-ζ ^ 2 / 2)) ∧
    histMeasure ν z ψ t
        {h | ζ * σ₀ * wnorm (Cmat (armsOf h)) (ψ.act t h - x) <
          inner ℝ (ψ.act t h - x) (Zhat h - z)} ≤
      ENNReal.ofReal ((t : ℝ) ^ (5 * 𝒰.ncard) * Real.exp (-ζ ^ 2 / 2)) := by sorry

end LinParamBandits.UEGeneral
