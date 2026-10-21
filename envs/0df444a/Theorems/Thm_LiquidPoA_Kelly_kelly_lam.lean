-- Prove2me | Theorems.Thm_LiquidPoA_Kelly_kelly_lam
-- name    : LiquidPoA.Kelly.kelly_lam
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:56.402365+00:00
-- url     : https://prove2.me/theorems/27a5ee17-6fe5-4958-9c9e-01af02c3a9da
-- title:
--   p. 9 — Kelly derivative coefficient
-- statement:
--   For a Kelly signal vector $s\in\mathbb X_n$, fix a player $i$ and write $C_i=\sum_{t\ne i}s_t$. The inverse own-signal allocation derivative times the own-signal payment derivative is
--
--   $$
--   \lambda_i^{Kelly}(s)=\frac{(s_i+C_i)^2}{C_i}.
--   $$
--
--   This coefficient is the slope of player $i$'s valuation in the affine game $G^{Kelly}(s,j)$. Because $s\in\mathbb X_n$, $C_i>0$ for every player.
-- source:
--   Caragiannis, Voudouris, The efficiency of resource allocation mechanisms for budget-constrained users, arXiv:1707.03551v3, p. 9, display following the definition of G^M(s,j)

import Mathlib
import Definitions.Def_LiquidPoA_Kelly_Setting

namespace LiquidPoA.Kelly

/-- The displayed formula for `λᵢ` of the Kelly mechanism on p. 9. -/
theorem kelly_lam {n : ℕ} (s : Fin n → ℝ) (hs : InX s) (i : Fin n) :
    lam (kelly n) s i =
      (s i + ∑ t ∈ Finset.univ.erase i, s t) ^ 2 /
        (∑ t ∈ Finset.univ.erase i, s t) := by sorry

end LiquidPoA.Kelly
