-- Prove2me | Theorems.Thm_LefebvreVariations_kirszbraun_plane_to_plane
-- name    : LefebvreVariations.kirszbraun_plane_to_plane
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:24:01.623442+00:00
-- url     : https://prove2.me/theorems/c231989f-82c8-4026-a453-8bf1c04ab48f
-- title:
--   Lefebvre's variations, No. 267 — on a theme by Kirszbraun: a Lipschitz map from a subset of the plane to the plane extends with the same constant
-- statement:
--   Let $A\subseteq\mathbb{R}^2$ be any set (possibly empty or infinite), let $\lambda\ge0$, and let $f:\mathbb{R}^2\to\mathbb{R}^2$ satisfy
--   $$
--   \|f(x)-f(y)\|\le\lambda\,\|x-y\|\qquad\text{for all }x,y\in A .
--   $$
--   Then there is a map $F:\mathbb{R}^2\to\mathbb{R}^2$ with
--   $$
--   F=f\ \text{on }A,\qquad \|F(x)-F(y)\|\le\lambda\,\|x-y\|\quad\text{for all }x,y\in\mathbb{R}^2 ,
--   $$
--   where $\|\cdot\|$ is the Euclidean norm.
--
--   This is Kirszbraun's extension theorem in the first case where both the source and the target are genuinely multi-dimensional, $D=D'=2$; the constant $\lambda$ is preserved, unlike what a coordinatewise McShane extension would give (it would lose a factor up to $\sqrt2$). It is the form used for planar Euclidean Steiner tree arguments.
--
--   **Formalization Note** Both spaces are `EuclideanSpace ℝ (Fin 2)`; `f` is defined on the whole plane and only its values on `A` matter (`LipschitzOnWith K f A`); `K` is an `NNReal`. The conclusion is `∃ F, LipschitzWith K F ∧ Set.EqOn F f A`. This is `SteinerAPX.kirszbraun` with `ι := Fin 2` and `ι' := Fin 2`.
--
--   **Why this is a variation.** This varies the open platform problem SteinerAPX.kirszbraun (Kirszbraun's extension theorem for A in R^D, maps into R^D' with the same Lipschitz constant). It is the planar case D = D' = 2, the first case where a coordinatewise McShane extension loses a factor and the Euclidean structure of the target is really needed, stated in the parent's own formulation.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   M. D. Kirszbraun, Ueber die zusammenziehende und Lipschitzsche Transformationen, Fund. Math. 22 (1934) 77-108; F. A. Valentine, A Lipschitz condition preserving extension for a vector function, Amer. J. Math. 67 (1945) 83-93 (Hilbert-space form); both cited from memory, page numbers not verified. Origin of this statement: the case D = D' = 2 of the platform theorem SteinerAPX.kirszbraun, which quotes Kirszbraun's theorem from the manuscript of S. Bartlmae on Euclidean Steiner tree.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- **Kirszbraun extension in the plane.** If `A ⊆ ℝ²` and `f : A → ℝ²` is `λ`-Lipschitz, then `f` extends to a
`λ`-Lipschitz map `F : ℝ² → ℝ²` with the same constant. This is Kirszbraun's theorem (Kirszbraun, *Über die
zusammenziehende und Lipschitzsche Transformationen*, Fund. Math. 22 (1934); Valentine, Amer. J. Math. 67 (1945) for the
Hilbert-space form; both cited from memory) in the first genuinely multi-dimensional case `D = D' = 2`, the one used
for planar Steiner-tree arguments.

**Formalization Note.** Same statement as `SteinerAPX.kirszbraun` at `D = D' = 2`, using
`EuclideanSpace ℝ (Fin 2)` for both spaces; `f` is defined on the whole plane and only its values on `A` matter,
`A` may be empty or infinite. -/
theorem kirszbraun_plane_to_plane (A : Set (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) (K : NNReal)
    (hf : LipschitzOnWith K f A) :
    ∃ F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2), LipschitzWith K F ∧ Set.EqOn F f A := by
  sorry

end LefebvreVariations
