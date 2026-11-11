-- Prove2me | Theorems.Thm_MixedVolFPRAS_Main_theorem_2_13
-- name    : MixedVolFPRAS.Main.theorem_2_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:30:47.573746+00:00
-- url     : https://prove2.me/theorems/f4577a22-069c-4141-b5e3-848438df2064
-- title:
--   Theorem 2.13 — V(K,K,C)·V(J,L,C) ≤ 2·V(J,K,C)·V(K,L,C) for convex bodies
-- statement:
--   Let $n\ge2$ and let $J,K,L,C_1,\dots,C_{n-2}$ be convex bodies in $\mathbb{R}^n$; write $C=(C_1,\dots,C_{n-2})$ and $V_n(A,B,C)=V_n(A,B,C_1,\dots,C_{n-2})$. Then
--
--   $$V_n(K,K,C)\cdot V_n(J,L,C)\le 2\cdot V_n(J,K,C)\cdot V_n(K,L,C).$$
--
--   This reverse Alexandrov–Fenchel-type inequality (Brazitikos–Giannopoulos–Liakopoulos) is what makes the balancing lemmas of §5 work: it controls how the mixed volume changes when one body is replaced by another.
--
--   Differences from the source:
--   - encoding: the tuple $C$ has $n-2$ entries → `2 ≤ n` is a binder and the tuple is `tuple2 a b C`; reason: the statement needs $n\ge2$ to have the two distinguished slots.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 10, Theorem 2.13

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_MixedVolume

namespace MixedVolFPRAS.Main

/-- **Theorem 2.13** ([BGL18]). For convex bodies `J, K, L, C₁, …, C_{n−2}` in `ℝⁿ` (`n ≥ 2`),
`Vₙ(K, K, C) · Vₙ(J, L, C) ≤ 2 · Vₙ(J, K, C) · Vₙ(K, L, C)`. -/
theorem theorem_2_13 {n : ℕ} (hn : 2 ≤ n) (J K L : Set (E n)) (C : Fin (n - 2) → Set (E n))
    (hJ : IsConvexBody J) (hK : IsConvexBody K) (hL : IsConvexBody L)
    (hC : ∀ i, IsConvexBody (C i)) :
    mixedVolume (tuple2 K K C) * mixedVolume (tuple2 J L C) ≤
      2 * mixedVolume (tuple2 J K C) * mixedVolume (tuple2 K L C) := by sorry

end MixedVolFPRAS.Main
