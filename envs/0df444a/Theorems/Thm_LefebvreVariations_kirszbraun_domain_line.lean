-- Prove2me | Theorems.Thm_LefebvreVariations_kirszbraun_domain_line
-- name    : LefebvreVariations.kirszbraun_domain_line
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:23:46.147559+00:00
-- url     : https://prove2.me/theorems/a41a4007-4cf4-42a7-858f-835bb084ad5a
-- title:
--   Lefebvre's variations, No. 266 — on a theme by Kirszbraun: a Lipschitz map from a subset of the line into Euclidean space extends with the same constant
-- statement:
--   Let $D'\ge0$, let $A\subseteq\mathbb{R}$ be any set (possibly empty or infinite), let $\lambda\ge0$, and let $f:\mathbb{R}\to\mathbb{R}^{D'}$ satisfy
--   $$
--   \|f(x)-f(y)\|\le\lambda\,|x-y|\qquad\text{for all }x,y\in A .
--   $$
--   Then there is a map $F:\mathbb{R}\to\mathbb{R}^{D'}$ with
--   $$
--   F=f\ \text{on }A,\qquad \|F(x)-F(y)\|\le\lambda\,|x-y|\quad\text{for all }x,y\in\mathbb{R}.
--   $$
--
--   This is Kirszbraun's extension theorem for Lipschitz maps into Euclidean space, in the smallest source dimension $D=1$. For $D'=1$ it is McShane's extension $F(x)=\inf_{a\in A}\bigl(f(a)+\lambda|x-a|\bigr)$; for $D'\ge2$ the constant $\lambda$ is not preserved by extending coordinatewise (one gets $\sqrt{D'}\,\lambda$), which is why the Euclidean structure of the target matters.
--
--   **Formalization Note** The source is `EuclideanSpace ℝ (Fin 1)` and the target `EuclideanSpace ℝ ι'` for a finite type `ι'`; `f` is defined on the whole source and only its values on `A` matter (`LipschitzOnWith K f A`); `K` is an `NNReal`. The conclusion is `∃ F, LipschitzWith K F ∧ Set.EqOn F f A`. This is `SteinerAPX.kirszbraun` with `ι := Fin 1`.
--
--   **Why this is a variation.** This varies the open platform problem SteinerAPX.kirszbraun (Kirszbraun's extension theorem for A in R^D, maps into R^D' with the same Lipschitz constant). It is the case of source dimension D = 1 for every target dimension D', in the parent's own formulation; for D' = 1 it is McShane's theorem, so it is a natural first step towards the general case.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   M. D. Kirszbraun, Ueber die zusammenziehende und Lipschitzsche Transformationen, Fund. Math. 22 (1934) 77-108; E. J. McShane, Extension of range of functions, Bull. Amer. Math. Soc. 40 (1934) 837-842 (for the real-valued case); both cited from memory, page numbers not verified. Origin of this statement: the case D = 1 of the platform theorem SteinerAPX.kirszbraun, which quotes Kirszbraun's theorem from the manuscript of S. Bartlmae on Euclidean Steiner tree.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- **Kirszbraun extension from a subset of the line.** If `A ⊆ ℝ` and `f : A → ℝ^{D'}` is `λ`-Lipschitz, then `f`
extends to a `λ`-Lipschitz map `F : ℝ → ℝ^{D'}`, with the same constant, for every `D'`. This is Kirszbraun's
theorem (Kirszbraun, *Über die zusammenziehende und Lipschitzsche Transformationen*, Fund. Math. 22 (1934); cited
from memory) in the smallest source dimension `D = 1`; for `D' = 1` it is McShane's extension.

**Formalization Note.** Same statement as `SteinerAPX.kirszbraun` with the source `EuclideanSpace ℝ (Fin 1)` and
an arbitrary finite target `EuclideanSpace ℝ ι'`; `f` is defined on the whole line and only its values on `A` matter,
`A` may be empty or infinite, and the constant `K` is an `NNReal`. -/
theorem kirszbraun_domain_line {ι' : Type} [Fintype ι'] (A : Set (EuclideanSpace ℝ (Fin 1)))
    (f : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ ι') (K : NNReal) (hf : LipschitzOnWith K f A) :
    ∃ F : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ ι', LipschitzWith K F ∧ Set.EqOn F f A := by
  sorry

end LefebvreVariations
