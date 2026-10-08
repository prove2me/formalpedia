-- Prove2me | Theorems.Thm_LinParamBandits_UEGeneral_martingale_loewner
-- name    : LinParamBandits.UEGeneral.martingale_loewner
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:27.50238+00:00
-- url     : https://prove2.me/theorems/20815662-96cd-4cda-a0d8-8138c2f57fd1
-- title:
--   Lemma B.5 — M_tM_t′ ≤ ζ²κ₀²σ₀²(log t)C_t^{-1} with high probability
-- statement:
--   Consider a run of the UE policy under Assumption 1. For every $t \ge r$ and every $\zeta \ge 2$,
--   $$\Pr\Big\{M_tM_t' \le \zeta^2\kappa_0^2\sigma_0^2(\log t)\,C_t^{-1}\Big\} \ge 1 - t^{r\kappa_0^2}e^{-\zeta^2/4},$$
--   where $A \le B$ means that $B - A$ is positive semidefinite and $C_t^{-1} = \sum_{s=1}^t U_sU_s'$.
--
--   The matrix inequality controls $x'M_t$ in all directions simultaneously; it is the step from Lemma B.4 to Theorem B.2.
--
--   **Formalization Note** The statement is about a run of the UE policy (`IsUE`) under Assumption 1 (`Assumption1`) on a compact nonempty arm set $\mathcal U_r \subset \mathbb R^r$, $r \ge 2$, with noise laws given by a Markov kernel $\nu$ (the law of $W^u_t$ is $\nu(u)$ for every $t$). "$\Pr\{\cdot \mid Z = z\}$" is the law `histMeasure ν z ψ t` of the history $(U_1, X_1, \dots, U_t, X_t)$ with the parameter fixed to $z$; $U_{t+1}$ is `ψ.act t h`. $C_t$ is `Cmat`, the inverse of the design matrix $\sum_{s \le t} U_s U_s'$, which is positive definite on every history that starts with $b_1, \dots, b_r$ (all histories of a UE run, since $t \ge r$). The probability is taken given $Z = z$, for every $z$ (the form used in the proof of Theorem B.2). The Loewner order is `Matrix.PosSemidef` of the difference; $M_tM_t'$ is `vecMulVec M M`. When the right-hand side is negative the bound is trivial, as on the page.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Lemma B.5, p. 32

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy

namespace LinParamBandits.UEGeneral

open MeasureTheory ProbabilityTheory

/-- Lemma B.5 (p. 32): `M_t M_t′ ≤ ζ² κ₀² σ₀² (log t) C_t^{-1}` in the Loewner order with
probability at least `1 − t^{r κ₀²} e^{−ζ²/4}`, given `Z = z`. -/
theorem martingale_loewner {r : ℕ} (hr : 2 ≤ r) {𝒰 : Set (LinParamBandits.LowerBound.Vec r)} (h𝒰c : IsCompact 𝒰) (h𝒰n : 𝒰.Nonempty)
    {ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ} [IsMarkovKernel ν] {b : Fin r → LinParamBandits.LowerBound.Vec r} {σ₀ ubar lam0 : ℝ}
    (hA : Assumption1 𝒰 ν b σ₀ ubar lam0) {ψ : Policy r} (hψ : IsUE 𝒰 b σ₀ ubar lam0 ψ)
    (z : LinParamBandits.LowerBound.Vec r) (t : ℕ) (ht : r ≤ t) (ζ : ℝ) (hζ : 2 ≤ ζ) :
    ENNReal.ofReal (1 - (t : ℝ) ^ ((r : ℝ) * kappa0 ubar lam0 ^ 2) * Real.exp (-ζ ^ 2 / 4)) ≤
      histMeasure ν z ψ t
        {h | ((ζ ^ 2 * kappa0 ubar lam0 ^ 2 * σ₀ ^ 2 * Real.log t) • design (armsOf h) -
            Matrix.vecMulVec (Mvec z h).ofLp (Mvec z h).ofLp).PosSemidef} := by sorry

end LinParamBandits.UEGeneral
