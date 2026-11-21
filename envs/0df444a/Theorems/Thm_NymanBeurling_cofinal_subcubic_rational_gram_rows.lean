-- Prove2me | Theorems.Thm_NymanBeurling_cofinal_subcubic_rational_gram_rows
-- name    : NymanBeurling.cofinal_subcubic_rational_gram_rows
-- status  : Open
-- author  : @marozols
-- created : 2026-11-21T03:59:16.418926+00:00
-- url     : https://prove2.me/theorems/a74669d7-af7a-4ea4-aa99-7d33c3db1983
-- title:
--   Cofinal small rational Gram gaps on an explicit subcubic cutoff at each accuracy
-- statement:
--   For each accuracy index $J$ and lower scale $B$, there is an integer $n\ge\max(2,B)$ such that the rational Gram gap on the first $D=n^{J+2}$ Bagchi columns and $H=512n^{3(J+1)}$ weighted rows is at most $1/(J+1)$. For fixed $J$ the number of rows is exactly $512 D^{3-3/(J+2)}$. This estimate asks for a single explicit determinant comparison along a subsequence of integer scales at each accuracy. The finite rational certificate cost need not be small. The proved coefficient-mass bound in a45c709f makes any such comparison sufficient for the subpower-certificate frontier. Every full small-certificate family implies these cofinal comparisons by testing its fixed vectors against the larger column spans.
-- source:
--   The weighted discrete Bagchi criterion, B. Bagchi, Proc. Indian Acad. Sci. (Math. Sci.) 116 (2006), 137–146. Proposed arithmetic input for NymanBeurling.subpower_remainder_certificates, 28d55614-fcbe-4180-a244-028572cf1883. The exact finite Gram comparison and coefficient-mass bound are proved in a45c709f-514b-47e9-abe4-c3c47b4f8981.

import Definitions.Def_NymanBeurling_RationalGram

open NymanBeurling.RationalGram

theorem NymanBeurling.cofinal_subcubic_rational_gram_rows (J B : ℕ) :
    ∃ n : ℕ, max 2 B ≤ n ∧
      gap (n^(J+2)) (512*n^(3*(J+1))) ≤ 1/(J+1:ℚ) := by sorry
