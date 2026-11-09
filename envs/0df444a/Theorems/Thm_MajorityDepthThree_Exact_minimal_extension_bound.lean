-- Prove2me | Theorems.Thm_MajorityDepthThree_Exact_minimal_extension_bound
-- name    : MajorityDepthThree.Exact.minimal_extension_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:37.077721+00:00
-- url     : https://prove2.me/theorems/4d87eb3a-81dd-4e1e-8b39-16a692e17312
-- title:
--   Lemma 4.1 — discounted minimal extensions
-- statement:
--   Let $F=G\wedge H$ be a valid $t$-threshold 3-CNF on a finite variable set $V$, where $H$ contains every positive clause and $G$ the remaining clauses. For each satisfying set $T\in T(H)$,
--
--   $$\sum_{U\in M(F),\ T\subseteq U}2^{-|U\setminus T|}\le1.$$
--
--   Here $M(F)$ denotes inclusion-minimal satisfying sets, including for signed formulas. The original ambient set is used for both $F$ and $H$. This discounted extension inequality is the capacity constraint underlying the packing relaxation.
--
--   Differences from the source:
--   - encoding: A finite ground set V and its subsets → Finite subsets V of a variable type, with finite families of subsets; reason: Every source instance has this representation; all assignments and ambient isolated variables are retained
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), p.10, Lemma 4.1

import Definitions.Def_MajorityDepthThree_Exact_Restrictions
import Definitions.Def_MajorityDepthThree_Exact_Circuits

set_option autoImplicit false

namespace MajorityDepthThree.Exact

theorem minimal_extension_bound {α : Type} [DecidableEq α] (V : Finset α)
    (F : CNF α) (t : ℕ) (hv : ValidCNF V F) (hw : Width 3 F)
    (ht : Threshold V F t) (T : Finset α) (hT : T ∈ transversals V (positivePart F)) :
    (∑ U ∈ (minimalSets V F).filter (fun U => T ⊆ U),
      (2 : ℝ) ^ (-(U \ T).card : ℤ)) ≤ 1 := by sorry

end MajorityDepthThree.Exact
