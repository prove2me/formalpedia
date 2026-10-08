-- Prove2me | Theorems.Thm_HallReps_CDR_theorem1_hall
-- name    : HallReps.CDR.theorem1_hall
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:09:16.744027+00:00
-- url     : https://prove2.me/theorems/a545816e-bab7-4d08-8911-b41715b328dc
-- title:
--   Theorem 1, p. 27 — Hall's condition suffices for a complete system of distinct representatives of a finite system of arbitrary sets
-- statement:
--   Let $S$ be any set and let $T_i$ ($i \in I$) be a finite system of subsets of $S$; the sets may be infinite and need not be distinct. Suppose that any $k$ of the sets contain between them at least $k$ elements of $S$:
--   $$|J| \le \Bigl|\bigcup_{i \in J} T_i\Bigr| \qquad \text{for every } J \subseteq I.$$
--   Then the system has a complete set of distinct representatives: there are pairwise distinct elements $a_i \in T_i$ ($i \in I$).
--
--   This is Hall's marriage theorem in its original form. The condition is obviously necessary (p. 27); Theorem 1 is the sufficiency. It is the step from which Theorems 2 and 3 are deduced.
--
--   **Formalization Note.** The system is `T : ι → Set α` with `[Finite ι]`; the sets are `Set α`, not `Finset α`, and Hall's condition is measured with `Set.encard` in `ℕ∞`. Restricted to finite sets this is Mathlib's `Finset.all_card_le_biUnion_card_iff_existsInjective'`; the platform's proved `YogeshwaranDM.sdr_iff` states the equivalence of Hall's condition with the existence of a C.D.R. for arbitrary sets and a `Fintype` index type, which contains this theorem as one direction.
-- source:
--   P. Hall, On representatives of subsets, J. London Math. Soc. 10 (1935), p. 27, Theorem 1

import Mathlib
import Definitions.Def_HallReps_CDR_System

namespace HallReps.CDR

theorem theorem1_hall {ι α : Type*} [Finite ι] (T : ι → Set α) (h : HallCondition T) :
    ∃ a : ι → α, IsCDR T a := by sorry

end HallReps.CDR
