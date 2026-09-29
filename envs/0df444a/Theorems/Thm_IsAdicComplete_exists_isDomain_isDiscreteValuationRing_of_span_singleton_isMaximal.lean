-- Prove2me | Theorems.Thm_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_singleton_isMaximal
-- name    : IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_span_singleton_isMaximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/14333bad-0fa1-5461-8c8f-6af19c5bd8c5
-- title:
--   Complete ring with maximal principal ideal is a DVR
-- statement:
--   Let $\mathcal O$ be a commutative ring and $\varpi \in \mathcal O$ an element that is a non-zero-divisor (a member of the submonoid $\mathrm{nonZeroDivisors}\,\mathcal O$). Assume that the principal ideal $(\varpi) = \mathcal O\varpi$ is maximal and that $\mathcal O$ is $(\varpi)$-adically complete in Mathlib's sense, i.e. `IsAdicComplete (Ideal.span {ϖ}) 𝓞`, which combines separatedness (the intersection of the ideals $(\varpi)^n\mathcal O$ is zero, stated as `IsHausdorff`) with precompleteness (every sequence that is Cauchy for the $(\varpi)$-adic filtration has a limit). The conclusion asserts the existence of a proof that $\mathcal O$ is an integral domain and, relative to that domain structure, of a proof that $\mathcal O$ is a discrete valuation ring — so in particular a local principal ideal domain that is not a field — such that, with respect to the local ring structure carried by this discrete valuation ring instance, $\varpi$ is irreducible in $\mathcal O$ and the maximal ideal of $\mathcal O$ equals $(\varpi)$; thus $\varpi$ is a uniformiser. The existential quantifiers over the `IsDomain` and `IsDiscreteValuationRing` data are what makes the final two assertions typecheck.
--
--   This is the standard criterion identifying a $\varpi$-adically complete and separated ring whose ideal $(\varpi)$ is maximal, with $\varpi$ a non-zero-divisor, as a complete discrete valuation ring with uniformiser $\varpi$. It supplies the coefficient rings used in the deformation-theoretic and Hecke-algebra parts of the argument, and is invoked by [`IsDiscreteValuationRing.exists_isAdicComplete_map_maximalIdeal_eq_forall_sub_mem_maximalIdeal`](thm.html#IsDiscreteValuationRing.exists_isAdicComplete_map_maximalIdeal_eq_forall_sub_mem_maximalIdeal) and by [`IsLocalRing.exists_isDiscreteValuationRing_ringHom_of_finite_residueField`](thm.html#IsLocalRing.exists_isDiscreteValuationRing_ringHom_of_finite_residueField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_singleton_isMaximal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_span_singleton_isMaximal
    {𝓞 : Type u} [CommRing 𝓞] (ϖ : 𝓞) (hϖ : ϖ ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {ϖ}).IsMaximal] [IsAdicComplete (Ideal.span {ϖ}) 𝓞] :
    ∃ (_ : IsDomain 𝓞) (_ : IsDiscreteValuationRing 𝓞),
      Irreducible ϖ ∧ IsLocalRing.maximalIdeal 𝓞 = Ideal.span {ϖ} := by sorry
