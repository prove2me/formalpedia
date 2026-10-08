-- Prove2me | Theorems.Thm_LostSalesOldNew_StateReduction_Xs_invariant
-- name    : LostSalesOldNew.StateReduction.Xs_invariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:31.541438+00:00
-- url     : https://prove2.me/theorems/63489a69-bedf-485b-80b6-8cf04b94a276
-- title:
--   Proof of Claim 1 — under a policy in Z(s), x ∈ X(s) implies x₊ ∈ X(s) for every demand d ≥ 0
-- statement:
--   Let $L\ge 1$. Let $s=(s_0,\dots,s_L)$ satisfy $s_0\ge s_1\ge\dots\ge s_L\ge 0$, let $z\in Z(s)$, let $x\in X(s)$, and let $d\ge 0$ be a demand. Then the next state
--   $$
--   x_+ = \bigl([x_0-d]^+ + x_1,\ x_2,\ \dots,\ x_{L-1},\ z(x)\bigr)
--   $$
--   again lies in $X(s)$. In the paper's words: once the process enters $X(s)$, it never leaves.
--
--   This is the invariance half of the proof of Claim 1.
--
--   **Formalization Note.** The transition is `next x (z x) d`. The positive lead time is the standing assumption of §2.
-- source:
--   Zipkin, Old and New Methods for Lost-Sales Inventory Systems, Operations Research 56(5) (2008), proof of Claim 1, p. 1259

import Mathlib
import Definitions.Def_LostSalesOldNew_StateReduction_Model

namespace LostSalesOldNew.StateReduction

theorem Xs_invariant {L : ℕ} (hL : 0 < L)
    (s : Fin (L + 1) → ℝ) (hs : IsLevelVector s)
    (z : (Fin L → ℝ) → ℝ) (hz : z ∈ Zs s) (x : Fin L → ℝ) (hx : x ∈ Xs s)
    (d : ℝ) (hd : 0 ≤ d) :
    next x (z x) d ∈ Xs s := by sorry

end LostSalesOldNew.StateReduction
