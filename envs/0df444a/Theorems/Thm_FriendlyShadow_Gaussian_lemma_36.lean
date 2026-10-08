-- Prove2me | Theorems.Thm_FriendlyShadow_Gaussian_lemma_36
-- name    : FriendlyShadow.Gaussian.lemma_36
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:16:43.880916+00:00
-- url     : https://prove2.me/theorems/dec903c1-fcc5-4513-9e68-710490aa3585
-- title:
--   Lemma 36, p. 27 — length((x + q + ω̄ℝ) ∩ conv(b₁,…,b_d)) = ‖C(q)‖₁ · |Σ zᵢhᵢ|
-- statement:
--   Let $d\ge3$, $b_1,\dots,b_d\in V$, and $\bar\omega\in V$ a unit vector. Put $h_i=\bar\omega^\mathsf{T}b_i$, $x=\pi_{\bar\omega^\perp}(b_1)$ and $(s_1,\dots,s_d)=S(b_1,\dots,b_d)$, the projected shape, and assume $\operatorname{rank}(s_2,\dots,s_d)=d-2$ (the shape is allowed). Let $z$ be a kernel combination of the shape. Then for every $q\in\operatorname{conv}(S)$,
--   $$\operatorname{length}\big((x+q+\bar\omega\cdot\mathbb R)\cap\operatorname{conv}(b_1,\dots,b_d)\big)=\|C(q)\|_1\cdot\Big|\sum_{i=1}^d z_ih_i\Big| .$$
--
--   The length of a chord parallel to $\bar\omega$ thus factors into a "shape" term and a "height" term. Lemmas 39 and 41 bound the expectations of these two terms separately.
--
--   **Formalization Note** The length of the chord is its diameter; the chord is compact, so the diameter is finite. The rank condition is the one in the definition of the allowed shapes $\mathcal S$, under which $z$ is unique up to sign (the absolute value removes the sign).
-- source:
--   Dadush & Huiberts, arXiv:1711.05667v4, Lemma 36, p. 27

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Shape

open scoped RealInnerProductSpace

namespace FriendlyShadow.Gaussian

/-- Lemma 36 (p. 27). Let `b₁, …, b_d ∈ V`, `ω̄` a unit vector, `hᵢ = ω̄ᵀbᵢ`,
`(s₁, …, s_d) = S(b₁, …, b_d)` the shape (with `rank(s₂, …, s_d) = d − 2`), `x = π_{ω̄⊥}(b₁)` and
`z` a kernel combination of the shape. For every `q ∈ conv(S)`,
`length((x + q + ω̄ · ℝ) ∩ conv(b₁, …, b_d)) = ‖C(q)‖₁ · |Σ zᵢhᵢ|`, the length of the (compact)
chord being its diameter. -/
theorem lemma_36 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {d : ℕ}
    [NeZero d] (hd : 3 ≤ d) (b : Fin d → V) (ω : V) (hω : ‖ω‖ = 1)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range (shapeOf ω b))) = d - 2)
    (z : Fin d → ℝ) (hz : IsKernelComb (shapeOf ω b) z)
    (q : V) (hq : q ∈ convexHull ℝ (Set.range (shapeOf ω b))) :
    Metric.diam ({p | ∃ t : ℝ, p = projPerp ω (b 0) + q + t • ω} ∩
        convexHull ℝ (Set.range b)) =
      chordLen (shapeOf ω b) q * |∑ i, z i * ⟪ω, b i⟫| := by sorry

end FriendlyShadow.Gaussian
