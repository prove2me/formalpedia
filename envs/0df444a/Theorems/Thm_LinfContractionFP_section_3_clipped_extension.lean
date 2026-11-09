-- Prove2me | Theorems.Thm_LinfContractionFP_section_3_clipped_extension
-- name    : LinfContractionFP.section_3_clipped_extension
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:15:17.5122+00:00
-- url     : https://prove2.me/theorems/7ec0a72f-5b14-4072-9ff7-be98c1737ca2
-- title:
--   Section 3 — the clipped extension preserves $\gamma$ and the fixed point
-- statement:
--   Let $0<\gamma\le1$ and let $f$ be a $(1-\gamma)$-contraction of $[0,1]^d$ in the $\ell_\infty$ norm. Extend $f$ to $\mathbb R^d$ by $\bar f(x)=f(\mathrm{clip}_{[0,1]^d}(x))$. Then:
--
--   1. $\bar f$ is a $(1-\gamma)$-contraction of all of $\mathbb R^d$: $\|\bar f(x)-\bar f(y)\|_\infty\le(1-\gamma)\|x-y\|_\infty$ for all $x,y\in\mathbb R^d$;
--   2. the fixed points of $\bar f$ in $\mathbb R^d$ are exactly the fixed points of $f$ in $[0,1]^d$;
--   3. $\bar f$ has exactly one fixed point.
--
--   This justifies the paper's standing convention of evaluating $f$ outside the cube.
--
--   Differences from the source:
--   - reading: this extension preserves the contraction gap γ and the unique fixed point x* → three clauses: contraction on all of ℝ^d, same fixed points, exactly one fixed point; reason: the sentence's two claims, with 'unique' made explicit
--   - encoding: f extended in place → a separate map clipExt f; reason: Lean convention; same map
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Section 3, p.5

import Mathlib
import Definitions.Def_LinfContractionFP_IsContraction
import Definitions.Def_LinfContractionFP_clipExt

namespace LinfContractionFP

/-- Section 3: the clipped extension `x ↦ f(clip[0,1]^d(x))` of a `(1 − γ)`-contraction `f` of
the cube is a `(1 − γ)`-contraction of all of `ℝ^d`, its fixed points are exactly the fixed
points of `f` in the cube, and it has exactly one fixed point.

Soleymani–Farina, *A Quasipolynomial Algorithm for ℓ∞ Contractions*, arXiv:2610.30122 (held
version, sha256 595b4493…), Section 3, p.5: "For that, throughout the paper we extend f to R^d by setting
f(x) = f(clip[0,1]^d(x)) for x ∉ [0, 1]^d. Since clipping is ℓ∞-nonexpansive, this extension
preserves the contraction gap γ and the unique fixed point x*."

**Formalization Note.** "Preserves the contraction gap γ" is the first clause, "preserves the
unique fixed point x*" the second and third. -/
theorem section_3_clipped_extension {ι : Type} [Fintype ι] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (f : (ι → ℝ) → (ι → ℝ)) (hf : IsContraction γ f) :
    (∀ x y : ι → ℝ, ‖clipExt f x - clipExt f y‖ ≤ (1 - γ) * ‖x - y‖) ∧
      (∀ x : ι → ℝ, clipExt f x = x ↔ x ∈ unitCube ι ∧ f x = x) ∧
      (∃! x : ι → ℝ, clipExt f x = x) := by sorry

end LinfContractionFP
