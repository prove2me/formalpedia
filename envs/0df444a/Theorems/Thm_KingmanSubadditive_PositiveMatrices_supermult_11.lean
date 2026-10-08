-- Prove2me | Theorems.Thm_KingmanSubadditive_PositiveMatrices_supermult_11
-- name    : KingmanSubadditive.PositiveMatrices.supermult_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:59.426989+00:00
-- url     : https://prove2.me/theorems/ec5bf121-25e8-409c-bde2-c8307fbfc5e1
-- title:
--   (2.3.1) — [AB]₁₁ ≥ [A]₁₁[B]₁₁ for positive matrices
-- statement:
--   Let $A,B$ be $k\times k$ real matrices ($k\ge1$) with strictly positive entries. Then the $(1,1)$ entry is supermultiplicative:
--   $$[AB]_{11}\ \ge\ [A]_{11}[B]_{11}.$$
--
--   Kingman singles this property out as the core of the proof of the Furstenberg–Kesten theorem: it makes $-\log$ of the diagonal entry of a product subadditive.
--
--   **Formalization Note.** "Positive" means strictly positive entrywise, as in Theorem 5.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 893, §2.3, (2.3.1)

import Mathlib

namespace KingmanSubadditive.PositiveMatrices

/-- §2.3, (2.3.1), p. 893 (Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899
(1973)): the supermultiplicative property of the diagonal elements of positive matrices,
`[AB]₁₁ ≥ [A]₁₁[B]₁₁`.

**Formalization Note.** The paper's index `1` is `0 : Fin k` (so `k ≥ 1`, via `NeZero k`).
"Positive" is taken as strictly positive entrywise, as in Theorem 5. -/
theorem supermult_11 {k : ℕ} [NeZero k] (A B : Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    A 0 0 * B 0 0 ≤ (A * B) 0 0 := by sorry

end KingmanSubadditive.PositiveMatrices
