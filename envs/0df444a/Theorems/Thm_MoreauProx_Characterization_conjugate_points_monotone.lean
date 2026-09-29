-- Prove2me | Theorems.Thm_MoreauProx_Characterization_conjugate_points_monotone
-- name    : MoreauProx.Characterization.conjugate_points_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:19:05.413226+00:00
-- url     : https://prove2.me/theorems/4d3a25cf-8687-43c0-b754-38b869afc166
-- title:
--   (5.1) — conjugate pairs form a monotone relation: (x − x′ | y − y′) ≥ 0
-- statement:
--   Let $H$ be a real Hilbert space, $f \in \Gamma_0(H)$ and $g$ its dual function. If $x, y$ and $x', y'$ are two pairs of points conjugate with respect to $f$ and $g$, that is,
--   $$
--   f(x) + g(y) = (x \mid y), \qquad f(x') + g(y') = (x' \mid y'),
--   $$
--   then
--   $$
--   (x - x' \mid y - y') \ge 0.
--   $$
--
--   The relation "$y \in \partial f(x)$" is therefore monotone in the sense of Minty. Combined with Moreau's decomposition, this inequality yields the nonexpansiveness of $\operatorname{prox}_f$ (Proposition 5.b).
--
--   **Formalization Note** $f$ and $g$ are `EReal`-valued, and the conjugacy equalities are equalities in `EReal`.
-- source:
--   Moreau, Proximité et dualité dans un espace hilbertien, Bull. Soc. Math. France 93 (1965), p. 281, §5.a, (5.1)

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
open scoped InnerProductSpace

namespace MoreauProx.Characterization

theorem conjugate_points_monotone {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (hf : GammaZero f) (hg : g = conj f) (x y x' y' : H)
    (hxy : f x + g y = ((⟪x, y⟫_ℝ : ℝ) : EReal))
    (hxy' : f x' + g y' = ((⟪x', y'⟫_ℝ : ℝ) : EReal)) :
    0 ≤ ⟪x - x', y - y'⟫_ℝ := by sorry

end MoreauProx.Characterization
