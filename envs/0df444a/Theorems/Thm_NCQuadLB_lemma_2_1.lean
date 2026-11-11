-- Prove2me | Theorems.Thm_NCQuadLB_lemma_2_1
-- name    : NCQuadLB.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:13.396754+00:00
-- url     : https://prove2.me/theorems/b72dd4c3-b9f1-4e1d-bffd-61e363a65333
-- title:
--   Lemma 2.1 — $\mathrm{mindeg}(fg)=\mathrm{mindeg}(f)+\mathrm{mindeg}(g)$
-- statement:
--   Let $\mathbb F$ be a field. For all nonzero noncommutative polynomials $f,g$,
--
--   $$
--   \mathrm{mindeg}(fg)=\mathrm{mindeg}(f)+\mathrm{mindeg}(g).
--   $$
--
--   It is used to show that a product of more than $d$ factors without constant term has zero degree-$d$ projection.
--
--   Differences from the source:
--
--   - generalization: $f,g\in\mathbb F\langle X\rangle$, $X=\{x_1,\dots,x_n\}$ → $f,g$ in the free algebra $\mathbb F\langle V\rangle$ on any type $V$ of variables; reason: the case $V=X$ is the source's statement
--   - encoding: the minimum degree of a monomial appearing in $f$ → the infimum in $\mathbb N$ of the lengths of the words with nonzero coefficient; reason: equal for nonzero $f$, the only case stated
-- source:
--   Shastri, Willumsgaard, A Quadratic Lower Bound for Noncommutative Circuits, arXiv:2604.20575 (version of November 2, 2026, sha256 34159453…), Lemma 2.1, p.5

import Mathlib
import Definitions.Def_NCQuadLB_mindeg

namespace NCQuadLB

/-- **Lemma 2.1** (Shastri, Willumsgaard, *A Quadratic Lower Bound for Noncommutative Circuits*, arXiv:2604.20575, version of November 2, 2026, sha256 34159453…, p.5). For all nonzero `f, g ∈ F⟨X⟩`,
`mindeg(fg) = mindeg(f) + mindeg(g)`.

**Formalization Note** Stated for the free algebra `F⟨V⟩` over any field `F` on any type `V` of
noncommuting variables (`F⟨X⟩` is the case `V = X`). `mindeg` is the least length of a word with
nonzero coefficient. -/
theorem lemma_2_1 {F : Type*} [Field F] {V : Type*} (f g : FreeAlgebra F V) (hf : f ≠ 0)
    (hg : g ≠ 0) : mindeg (f * g) = mindeg f + mindeg g := by sorry

end NCQuadLB
