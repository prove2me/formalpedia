-- Prove2me | Theorems.Thm_LefebvreVariations_crc_quantile_leave_one_out_two_calibration
-- name    : LefebvreVariations.crc_quantile_leave_one_out_two_calibration
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:27:30.989743+00:00
-- url     : https://prove2.me/theorems/a867d25b-13f9-421d-886e-159706586b77
-- title:
--   Lefebvre's variations, No. 274 — on a theme by Angelopoulos, Bates, Fisch, Lei and Schuster: quantile risk control with two calibration points on a four-point grid, leave-one-out form
-- statement:
--   Let $\Lambda=\{0,1,2,3\}$, let $\alpha,\beta\in\mathbb R$ with $\beta\le1$, and let $L_0,L_1,L_2:\Lambda\to\mathbb R$ be non-increasing with $L_i(3)\le\alpha$. For each $i\in\{0,1,2\}$, with $\{j,k\}=\{0,1,2\}\setminus\{i\}$, put
--   $$
--   \hat\lambda_{(i)}=\min\Bigl\{\lambda\in\Lambda:\ \tfrac13\bigl(\mathbf 1[L_j(\lambda)>\alpha]+\mathbf 1[L_k(\lambda)>\alpha]\bigr)+\tfrac13\le1-\beta\Bigr\},
--   $$
--   with $\hat\lambda_{(i)}=3$ if the set is empty. Then
--   $$
--   \#\{\,i\in\{0,1,2\}:\ L_i(\hat\lambda_{(i)})>\alpha\,\}\ \le\ 3(1-\beta).
--   $$
--
--   In quantile risk control one chooses $\hat\lambda_\beta$ on $n$ calibration losses so that $\Pr\{L_{n+1}(\hat\lambda_\beta)>\alpha\}\le1-\beta$ for an exchangeable next loss. For three uniformly permuted losses that probability is the fraction of left-out indices counted above, so this is the case $n=2$ of the key inequality on a four-point grid, for arbitrary loss functions.
--
--   **Formalization Note** The parameter is the parent's `ConformalRiskControl.lhatQuantile` (imported from the parent's definitions) on `Λ = {0, 1, 2, 3} : Set ℝ`, with calibration losses `fun j : Fin 2 => L (i.succAbove j)`. The hypothesis `β ≤ 1` is needed (for `β > 1` the right side is negative while the left side is a count); no lower bound on `β` is needed. The count is a `Finset.card` of a filter over `Fin 3`, cast to `ℝ`.
--
--   **Why this is a variation.** A variation on the open platform problem ConformalRiskControl.quantile_risk_control (Proposition 4 of Conformal Risk Control: P(L_{n+1}(lhat_beta) > alpha) <= 1 - beta), played at n = 2 on a four-point parameter grid and as the deterministic leave-one-out count that the exchangeability argument reduces to. It uses the parent's own definition `lhatQuantile`. It is not a formal consequence of the parent, which concerns random exchangeable losses on a general parameter set.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Angelopoulos, Bates, Fisch, Lei and Schuster, Conformal Risk Control, arXiv:2208.02814 (identity of the paper and its quantile risk control extension confirmed; the section and proposition number are cited from memory). The leave-one-out form is the combinatorial core of the exchangeability argument (cited from memory). Checked here by hand (same monotonicity argument as for the expected-loss version) and exhaustively by exact rational arithmetic: all 64 patterns of exceedance thresholds of the three losses against 1 - beta on a grid of step 1/6 from 0 to 5 (1920 cases); the maximum of the count minus 3(1-beta) is 0.

import Mathlib
import Definitions.Def_ConformalRiskControl_Basic

set_option autoImplicit false

namespace LefebvreVariations

open ConformalRiskControl

/-- Quantile risk control with `n = 2` calibration points, in its exchangeability-free (leave-one-out) form on the four-point grid `Λ = {0, 1, 2, 3}`, for `β ≤ 1`.
The parameter `λ̂_β` of Section 4.2 of Angelopoulos–Bates–Fisch–Lei–Schuster, *Conformal Risk Control*, arXiv:2208.02814, is computed from every pair of the three non-increasing losses `L 0, L 1, L 2`; the number of left-out points whose loss exceeds `α` at the parameter computed without them is at most `3 (1 - β)`.
Source: Angelopoulos, Bates, Fisch, Lei, Schuster, *Conformal Risk Control*, Proposition 4 (number cited from memory). -/
theorem crc_quantile_leave_one_out_two_calibration (α β : ℝ) (hβ : β ≤ 1) (L : Fin 3 → ℝ → ℝ)
    (hanti : ∀ i, AntitoneOn (L i) ({0, 1, 2, 3} : Set ℝ))
    (hend : ∀ i, L i 3 ≤ α) :
    (((Finset.univ : Finset (Fin 3)).filter fun i : Fin 3 =>
        α < L i (lhatQuantile ({0, 1, 2, 3} : Set ℝ) α β (fun j : Fin 2 => L (i.succAbove j)))).card : ℝ)
      ≤ 3 * (1 - β) := by
  sorry

end LefebvreVariations
