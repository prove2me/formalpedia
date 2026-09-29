-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_isDiscreteValuationRing_coeffSubring
-- name    : ModularCurve.NodeLocalized.isDiscreteValuationRing_coeffSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/c913a2f9-0078-55a3-b62a-9dcf5e247951
-- title:
--   A ∩ K is a discrete valuation ring
-- statement:
--   Let $q$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$ (the algebraic closure of $\mathbb Q$), and let $k$ be a field of characteristic $q$. Suppose given a ring homomorphism $\mathrm{red} : A \to k$ whose zero set is exactly the maximal ideal of the local ring $A$, i.e. for every $c \in A$ one has $\mathrm{red}(c) = 0$ if and only if $c$ lies in $\mathrm{IsLocalRing.maximalIdeal}\,A$. Let $K$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$ which is finite-dimensional over $\mathbb Q$, that is, a number field inside $\overline{\mathbb Q}$. The assertion is that the subring $\mathrm{coeffSubring}\,A\,K$ of $\overline{\mathbb Q}$, defined as the intersection $A \cap K$ of the underlying subring of $A$ with the underlying subring of $K$, is a discrete valuation ring. The conclusion mentions only $A$ and $K$; the datum $(\mathrm{red}, k, q)$ and the description of its kernel enter only as the ambient hypotheses under which the statement is recorded.
--
--   Classically this identifies $A \cap K$ as the valuation ring of $K$ at the finite place induced by $A$, equivalently the localisation of the ring of integers $\mathcal O_K$ at a nonzero prime ideal, and hence as a discrete valuation ring. It supplies the `IsDiscreteValuationRing` hypothesis needed to extract uniformisers and ramification indices for the coefficient rings used in the local analysis of modular curves at a node, and is cited by the statements about reductions and about annulus and prolongation data in that analysis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_isDiscreteValuationRing_coeffSubring.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized

theorem ModularCurve.NodeLocalized.isDiscreteValuationRing_coeffSubring
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    IsDiscreteValuationRing ↥(coeffSubring A K) := by sorry
