-- Prove2me | Theorems.Thm_HryniewiczCriterion_exists_circle_param_of_image_eq
-- name    : HryniewiczCriterion.exists_circle_param_of_image_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T16:40:28.364463+00:00
-- url     : https://prove2.me/theorems/a7602a52-5bca-4356-914e-47d67a54cc75
-- title:
--   A periodic orbit traced by the boundary of an embedded disk lifts smoothly to the unit circle
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level, $P=(x,T)$ a periodic orbit of $X_H$ on $S$, and $e:\mathbb{R}^2\to\mathbb{R}^4$ a smooth map that restricts to an embedding of the closed unit disk (injective, with injective differential on the closed disk). If $e$ maps the unit circle onto the image $x(\mathbb{R})$, then there is a smooth $1$-periodic map $u:\mathbb{R}\to\mathbb{R}^2$ with values on the unit circle such that
--   $$e(u(s))=x(Ts)\qquad\text{for all } s\in\mathbb{R}.$$
--   Proof idea: $e$ restricted to the circle is a homeomorphism onto the compact set $x(\mathbb{R})$, so $u=(e|_{S^1})^{-1}\circ x(T\,\cdot)$ is continuous. Since $e\circ(\cos 2\pi t,\sin 2\pi t)$ is an immersion, it has smooth local left inverses near every point of the circle, so $u$ is smooth. Periodicity follows from $x(t+T)=x(t)$ and injectivity of $e$ on the circle.
-- source:
--   Standard (inverse function theorem for embedded curves); the parametrization step in U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, Proposition 2.1 (cited for necessity in Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, outline after Theorem 1.8).

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.exists_circle_param_of_image_eq (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (P : PeriodicOrbit H)
    (e : Plane → R4) (he : IsSmoothDiskEmbedding e) (hbd : e '' unitCircle = P.image) :
    ∃ u : ℝ → Plane, ContDiff ℝ ∞ u ∧ (∀ s, u (s + 1) = u s) ∧ (∀ s, u s ∈ unitCircle) ∧
      ∀ s, e (u s) = P.x (P.T * s) := by sorry
