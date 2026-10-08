-- Prove2me | Theorems.Thm_FriendlyShadow_Gaussian_lemma_35
-- name    : FriendlyShadow.Gaussian.lemma_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:16:31.731296+00:00
-- url     : https://prove2.me/theorems/83023cd4-f7fd-4af1-8553-3ded9f7e76f4
-- title:
--   Lemma 35, p. 27 — ‖C(q)‖₁ is concave on conv(S) and max_{q∈conv(S)} ‖C(q)‖₁ = ‖C(y)‖₁ = 2
-- statement:
--   Let $d\ge3$ and let $S=(s_1,\dots,s_d)$ be a shape: $s_1=0$ and $\operatorname{rank}(s_2,\dots,s_d)=d-2$. Let $z=z(S)$ be a kernel combination of $S$ (Definition 33) and
--   $$y=y(S)=\sum_{i=1}^d|z_i|\,s_i .$$
--   Then:
--   1. $q\mapsto\|C(q)\|_1$ is concave on $\operatorname{conv}(S)$;
--   2. $\|C(y)\|_1=2$ and $\|C(q)\|_1\le2$ for every $q\in\operatorname{conv}(S)$, i.e. $\max_{q\in\operatorname{conv}(S)}\|C(q)\|_1=\|C(y)\|_1=2$.
--
--   The function $\|C(q)\|_1$ measures the length of the chord of the simplex above $q$ relative to the longest such chord; these two properties drive the lower bound of Lemma 39.
--
--   **Formalization Note** The page says "with $z := z(S)$ as in Definition 34"; the kernel combination is Definition 33, which is what is used. The shape lives in a general real inner product space; the diameter condition of the allowed shapes is not needed and is omitted, so the statement covers every shape with the rank condition.
-- source:
--   Dadush & Huiberts, arXiv:1711.05667v4, Lemma 35, p. 27 (Defs 31, 33, 34, pp. 25–26)

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Shape

open scoped RealInnerProductSpace

namespace FriendlyShadow.Gaussian

/-- Lemma 35 (Properties of chord combinations, p. 27). Let `s = (s₁, …, s_d)` be a shape:
`s₁ = 0` and `rank(s₂, …, s_d) = d − 2`. Let `z` be a kernel combination of `s` and
`y = Σ |zᵢ| sᵢ`. Then `q ↦ ‖C(q)‖₁` is concave on `conv(S)`, `‖C(y)‖₁ = 2`, and
`‖C(q)‖₁ ≤ 2` for every `q ∈ conv(S)`. -/
theorem lemma_35 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {d : ℕ}
    [NeZero d] (hd : 3 ≤ d) (s : Fin d → V) (hs0 : s 0 = 0)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range s)) = d - 2)
    (z : Fin d → ℝ) (hz : IsKernelComb s z) :
    ConcaveOn ℝ (convexHull ℝ (Set.range s)) (chordLen s) ∧
      chordLen s (∑ i, |z i| • s i) = 2 ∧
      ∀ q ∈ convexHull ℝ (Set.range s), chordLen s q ≤ 2 := by sorry

end FriendlyShadow.Gaussian
