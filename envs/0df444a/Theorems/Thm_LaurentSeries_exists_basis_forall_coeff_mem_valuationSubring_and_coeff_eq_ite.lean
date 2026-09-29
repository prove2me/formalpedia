-- Prove2me | Theorems.Thm_LaurentSeries_exists_basis_forall_coeff_mem_valuationSubring_and_coeff_eq_ite
-- name    : LaurentSeries.exists_basis_forall_coeff_mem_valuationSubring_and_coeff_eq_ite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/3459187b-aede-51ca-a599-a2f4581bb0db
-- title:
--   Echelon basis with integral coefficients and unit pivots
-- statement:
--   Let $F$ be a field and let $O \subseteq F$ be a valuation subring which, as a ring, is a discrete valuation ring. Let $V$ be an $F$-subspace of the field of formal Laurent series $F((X))$ (Hahn series over $F$ with exponents in $\mathbb{Z}$), assumed finite-dimensional over $F$, and set $n = \operatorname{finrank}_F V$. The hypothesis `hbdd` is a bounded-denominators condition: for each $f \in V$ there is a nonzero $c \in F$ such that $c \cdot \operatorname{coeff}_m(f) \in O$ for every $m \in \mathbb{Z}$, i.e. the coefficients of $f$ have a common denominator with respect to $O$. The conclusion asserts the existence of a basis $b : \mathrm{Fin}\,n \to V$ of $V$ over $F$ together with a family of pivot exponents $p : \mathrm{Fin}\,n \to \mathbb{Z}$ such that, first, every coefficient $\operatorname{coeff}_m(b_i)$ lies in $O$ for all $i$ and all $m \in \mathbb{Z}$, and second, $\operatorname{coeff}_{p_i}(b_j) = 1$ if $i = j$ and $0$ otherwise. No injectivity of $p$ is asserted separately; it follows from the pivot relations.
--
--   This is the standard echelon ("cartesian", or $O$-adapted) basis of a finite-dimensional space of Laurent series with bounded denominators over a discretely valued field: integrality of all coefficients together with unit pivots forces the $b_i$ to span the $O$-lattice $V \cap O((X))$ and to remain independent modulo the maximal ideal of $O$. It is used in the construction of integral structures on spaces of $q$-expansions, and is cited by [`ModularCurve.exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular`](thm.html#ModularCurve.exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LaurentSeries_exists_basis_forall_coeff_mem_valuationSubring_and_coeff_eq_ite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LaurentSeries.exists_basis_forall_coeff_mem_valuationSubring_and_coeff_eq_ite
    {F : Type*} [Field F] (O : ValuationSubring F) [IsDiscreteValuationRing O]
    (V : Submodule F (LaurentSeries F)) [FiniteDimensional F V]
    (hbdd : ∀ f ∈ V, ∃ c : F, c ≠ 0 ∧ ∀ n : ℤ, c * (f : LaurentSeries F).coeff n ∈ O) :
    ∃ (b : Module.Basis (Fin (Module.finrank F V)) F V) (p : Fin (Module.finrank F V) → ℤ),
      (∀ (i : Fin (Module.finrank F V)) (n : ℤ), ((b i : V) : LaurentSeries F).coeff n ∈ O) ∧
      ∀ i j : Fin (Module.finrank F V),
        ((b j : V) : LaurentSeries F).coeff (p i) = if i = j then 1 else 0 := by sorry
