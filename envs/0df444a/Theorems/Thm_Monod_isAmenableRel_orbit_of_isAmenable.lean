-- Prove2me | Theorems.Thm_Monod_isAmenableRel_orbit_of_isAmenable
-- name    : Monod.isAmenableRel_orbit_of_isAmenable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T12:56:45.36417+00:00
-- url     : https://prove2.me/theorems/0925ff57-5711-4d6f-829c-3d2fd5a274cf
-- title:
--   p. 2 — a measurable action of a countable amenable group produces an amenable relation
-- statement:
--   Let $\Lambda$ be a countable amenable group acting on a measurable space $X$ with a σ-finite measure $\mu$, each element acting by a measurable map that pulls $\mu$-null sets back to $\mu$-null sets. Then the orbit equivalence relation $\{(x, \lambda x)\}$ is amenable (`IsAmenableRel`): it carries a left invariant mean in the sense of Connes–Feldman–Weiss (see the definitions bundle).
--
--   **Formalization Note.** The source says "measurable action"; the action is also assumed non-singular and $\mu$ σ-finite, the standing setting of the cited sources (CFW, Schmidt), in which amenability of a relation is defined; the source's "it follows from this definition" is meant in that setting. σ-finiteness matters: for counting measure, "almost everywhere" means everywhere, and a left invariant mean amounts to a Borel invariant assignment of means on the classes, which exists only for smooth relations (Kechris, *The Theory of Countable Borel Equivalence Relations*, Theorem 3.13), so the orbit relation of an irrational rotation, an action of the amenable group $\mathbf{Z}$, would not be amenable. The source's setting is a *measurable* equivalence relation, implicitly on a standard Borel space. The statement allows any measurable space $X$ and does not assert that the orbit relation is a measurable subset of $X \times X$, which the definition of amenability does not need and which can fail on an arbitrary measurable space. On a standard Borel space it is automatic: the relation is the union of the graphs of the countably many measurable maps $x \mapsto \lambda x$. The conclusion is amenability in the Connes–Feldman–Weiss operator form, the bundle's definition. The source recalls amenability (p. 2) as “an a.e. defined measurable assignment of a mean on the orbit of each point in such a way that the means of two equivalent points coincide”, a pointwise family of means, which gives an invariant mean in the operator form; for the pointwise form, the conclusion of this statement is known only assuming the continuum hypothesis (see the definitions bundle), so the statement asserts the operator form.
-- source:
--   Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110 (arXiv:1209.5229v2, whose page numbers are used), p. 2, before the proof of Theorem 1

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Monod_PiecewiseProjective

namespace Monod

theorem isAmenableRel_orbit_of_isAmenable {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite μ]
    (Λ : Type) [Group Λ] [Countable Λ] [MulAction Λ X]
    (hmeas : ∀ l : Λ, Measurable (fun x : X => l • x))
    (hnull : ∀ (l : Λ) (s : Set X), μ s = 0 → μ ((fun x : X => l • x) ⁻¹' s) = 0)
    (hΛ : Garrido.IsAmenable Λ) :
    IsAmenableRel μ {p : X × X | ∃ l : Λ, l • p.1 = p.2} := by
  sorry

end Monod
