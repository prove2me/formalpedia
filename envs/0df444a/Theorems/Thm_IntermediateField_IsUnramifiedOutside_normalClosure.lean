-- Prove2me | Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
-- name    : IntermediateField.IsUnramifiedOutside.normalClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/3428bef6-0113-5746-9ba5-f214cdcb111a
-- title:
--   Normal closure preserves being unramified outside S
-- statement:
--   Let $S$ be a finite set of rational primes and let $F$ be an intermediate field of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$, the algebraic closure of $\mathbb{Q}$ fixed by the project. Assume $F$ is unramified outside $S$ in the following sense: $F$ is finite-dimensional over $\mathbb{Q}$, and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the subgroup of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained as the image of the inertia subgroup of $A$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup of $A$ is contained in the fixing subgroup of $F$, i.e. fixes $F$ pointwise. The conclusion is that the normal closure of $F$ over $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ has the same two properties: it is finite-dimensional over $\mathbb{Q}$, and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ in which $q$ is a non-unit, that image of the inertia subgroup of $A$ lies in the fixing subgroup of the normal closure.
--
--   This is the compositum step in the bookkeeping of levels unramified outside $S$: it shows that the Galois (normal) levels are cofinal among the finite extensions of $\mathbb{Q}$ unramified outside $S$, which is what permits cochains on $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ that are constant modulo a level to be pushed through finite Galois quotients. It is used by the further results on enlarging unramified levels to normal ones and by the level-arithmetic constructions involving continuous $H^1$, $S$-units and $S$-class groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_IsUnramifiedOutside_normalClosure.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IntermediateField.IsUnramifiedOutside.normalClosure
    {S : Finset Nat.Primes} {F : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hF : F.IsUnramifiedOutside S) :
    (IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ)).IsUnramifiedOutside S := by sorry
