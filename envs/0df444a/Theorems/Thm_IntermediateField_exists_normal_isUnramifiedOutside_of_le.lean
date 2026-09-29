-- Prove2me | Theorems.Thm_IntermediateField_exists_normal_isUnramifiedOutside_of_le
-- name    : IntermediateField.exists_normal_isUnramifiedOutside_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/d9e0bc5c-8236-5b61-8d9e-46b86d265545
-- title:
--   Enlarging an extension unramified outside S to a normal one
-- statement:
--   Let $S$ be a finite set of rational primes and let $F$ be an intermediate field of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$, where $\overline{\mathbb{Q}}$ is the algebraic closure `AlgebraicClosure ℚ`. Assume $F$ satisfies `IsUnramifiedOutside S`, that is: $F$ is finite-dimensional over $\mathbb{Q}$, and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$ (so that $A$ lies over $q$), the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$, under the inclusion of the decomposition subgroup of $A$, is contained in the subgroup of automorphisms fixing $F$ pointwise. The conclusion asserts the existence of an intermediate field $L$ of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$ such that $F \le L$, such that $L$ again satisfies `IsUnramifiedOutside S` (in particular $L$ is finite-dimensional over $\mathbb{Q}$, and every inertia subgroup at every prime outside $S$ acts trivially on $L$), and such that $L$ is normal over $\mathbb{Q}$.
--
--   This is the statement that a finite extension of $\mathbb{Q}$ unramified outside $S$ can be enlarged to a finite normal (hence Galois) one unramified outside $S$ — the assertion that the normal closure of an $S$-unramified level is again an $S$-unramified level. It is used throughout the cohomological computations over number fields in the project, for instance to pass to a Galois splitting field when handling local invariants, inflation maps in degree two, and class group and unit contributions in degree one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_exists_normal_isUnramifiedOutside_of_le.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem IntermediateField.exists_normal_isUnramifiedOutside_of_le
    (S : Finset Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : F.IsUnramifiedOutside S) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), F ≤ L ∧ L.IsUnramifiedOutside S ∧ Normal ℚ L := by sorry
