-- Prove2me | Theorems.Thm_IntermediateField_isUnramifiedOutside_normalClosure__721fcc
-- name    : IntermediateField.isUnramifiedOutside_normalClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/721fccf3-aa03-5561-bdc9-ad515e610cf4
-- title:
--   Galois closure of an S-unramified level is S-unramified
-- statement:
--   Let $S$ be a finite set of rational primes and let $F$ be an intermediate field of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$ (the Mathlib algebraic closure of $\mathbb{Q}$), assumed to satisfy `IsUnramifiedOutside S`: that is, $F$ is finite-dimensional over $\mathbb{Q}$, and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ (transported from the decomposition subgroup by its inclusion) is contained in the subgroup fixing $F$ pointwise. The conclusion is a fourfold conjunction about $\tilde F =$ `normalClosure ℚ F (AlgebraicClosure ℚ)`, the normal closure of $F$ inside $\overline{\mathbb{Q}}$ viewed first as an intermediate field over $F$ and then, via `restrictScalars ℚ`, as an intermediate field of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$: firstly $F \le \tilde F$; secondly $\tilde F$ is finite-dimensional over $\mathbb{Q}$; thirdly $\tilde F/\mathbb{Q}$ is Galois; and fourthly $\tilde F$, as a $\mathbb{Q}$-intermediate field, again satisfies `IsUnramifiedOutside S` in the same inertia sense.
--
--   This packages the passage from a level unramified outside $S$ to a Galois such level: the normal closure of an $S$-unramified number field is again finite and $S$-unramified. It is invoked wherever a construction produces an $S$-level that must be enlarged to a Galois one, for instance in the level arithmetic used for principality of ideal classes, in $S$-unit computations, and in the statement on existence of Galois subextensions with controlled degree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_isUnramifiedOutside_normalClosure_1.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IntermediateField.isUnramifiedOutside_normalClosure
    (S : Finset Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hF : F.IsUnramifiedOutside S) :
    F ≤ (normalClosure ℚ ↥F (AlgebraicClosure ℚ)).restrictScalars ℚ ∧
    FiniteDimensional ℚ ↥(normalClosure ℚ ↥F (AlgebraicClosure ℚ)) ∧
    IsGalois ℚ ↥(normalClosure ℚ ↥F (AlgebraicClosure ℚ)) ∧
    ((normalClosure ℚ ↥F (AlgebraicClosure ℚ)).restrictScalars ℚ).IsUnramifiedOutside S := by sorry
