-- Prove2me | Theorems.Thm_MixedVolFPRAS_Main_lemma_5_4
-- name    : MixedVolFPRAS.Main.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:32:03.838002+00:00
-- url     : https://prove2.me/theorems/5725bf1d-fc7e-4fca-9190-52320b412432
-- title:
--   Lemma 5.4 — balanced rescaling keeps Z_β(t)/Z₀(t) within [1, 1/(1 − An²β)]
-- statement:
--   Let $K_1,\dots,K_n\subseteq\mathbb{R}^n$ be convex bodies and $t\in\mathbb{R}^n_{>0}$ such that $(t_1K_1,\dots,t_nK_n)$ is $A$-balanced for some $A\ge1$. Then for every $0\le\beta<1/(An^2)$,
--
--   $$1\le\frac{Z_\beta(t)}{Z_0(t)}\le\frac{1}{1-An^2\beta}.$$
--
--   Adding $\beta L(t)$ to every rescaled body well-rounds them while changing the mixed volume by a factor $1+O(An^2\beta)$ only; this is the approximation half of the simultaneous rounding of §5.
--
--   Differences from the source: none.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 24, Lemma 5.4

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_MixedVolume
import Definitions.Def_MixedVolFPRAS_Main_Balancing

open scoped Pointwise

namespace MixedVolFPRAS.Main

/-- **Lemma 5.4.** Let `K₁, …, Kₙ` be convex bodies and `t ∈ ℝⁿ_{>0}` such that
`(t₁K₁, …, tₙKₙ)` is `A`-balanced for some `A ≥ 1`. Then for every `0 ≤ β < 1/(An²)`,
`1 ≤ Z_β(t)/Z₀(t) ≤ 1/(1 − An²β)`. -/
theorem lemma_5_4 {n : ℕ} (K : Fin n → Set (E n)) (hK : ∀ i, IsConvexBody (K i))
    (t : Fin n → ℝ) (ht : ∀ i, 0 < t i) (A : ℝ) (hA : 1 ≤ A)
    (hbal : IsBalanced A (fun i => t i • K i)) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : β < 1 / (A * (n : ℝ) ^ 2)) :
    1 ≤ Zbeta K β t / Zbeta K 0 t ∧
      Zbeta K β t / Zbeta K 0 t ≤ 1 / (1 - A * (n : ℝ) ^ 2 * β) := by sorry

end MixedVolFPRAS.Main
