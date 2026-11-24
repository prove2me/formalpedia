-- Prove2me | Theorems.Thm_MonotoneCompStatics_QSMChar_Supplement_theorem2
-- name    : MonotoneCompStatics.QSMChar.Supplement.theorem2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:08:37.715938+00:00
-- url     : https://prove2.me/theorems/d02a97a5-edef-444c-a5e3-bd333a3b5620
-- title:
--   Theorem 2 — Common complete sublattice and union
-- statement:
--   Let $X$ be an arbitrary lattice and let $S,S'\subseteq X$ be nonempty. They are complete sublattices with $S\ge_s S'$ if and only if there is a complete sublattice $R$ and actual bounds $a=\inf S$, $b=\sup S'$ such that
--   $$S=R\cap[a,\infty),\qquad S'=R\cap(-\infty,b].$$
--   Moreover, their union is a complete sublattice whenever the left-hand conditions hold. This identifies the common lattice underlying two ordered constraint sets.
--
--   **Formalization Note** Complete means ambient closure under all nonempty-subset suprema and infima. The nonempty endpoint convention is explicit: the proof uses $\inf S\in S$ and $\sup S'\in S'$. No global completeness of $X$ is imposed.
--
--   Differences from the source:
--   - encoding: products and set-valued notation → curried functions, dependent profiles and predicates with actual extrema; reason: the order, quantifiers and all conclusion clauses are preserved
--   - reading: complete sublattices used with endpoint/existence claims → nonempty complete sublattices; reason: the source uses attained extrema in Theorem 2 and asserts existence of a maximum in A4; the empty set cannot satisfy those conclusions
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), DOI 10.2307/2951479, p.160, PDF 5, Theorem 2

import Mathlib
import Definitions.Def_Supermodularity_Lattices_Subcomplete
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

namespace MonotoneCompStatics.QSMChar.Supplement

theorem theorem2 {X : Type*} [Lattice X] (S S' : Set X)
    (hne : S.Nonempty) (hne' : S'.Nonempty) :
    ((Supermodularity.Lattices.Subcomplete S ∧ Supermodularity.Lattices.Subcomplete S' ∧
        Supermodularity.Lattices.InducedSetOrder S' S) ↔
      ∃ (R : Set X) (a b : X), Supermodularity.Lattices.Subcomplete R ∧
        IsGLB S a ∧ IsLUB S' b ∧ S = R ∩ Set.Ici a ∧ S' = R ∩ Set.Iic b) ∧
    ((Supermodularity.Lattices.Subcomplete S ∧ Supermodularity.Lattices.Subcomplete S' ∧
        Supermodularity.Lattices.InducedSetOrder S' S) →
      Supermodularity.Lattices.Subcomplete (S ∪ S')) := by sorry

end MonotoneCompStatics.QSMChar.Supplement
