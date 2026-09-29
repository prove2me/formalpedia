-- Prove2me | Theorems.Thm_NumberField_exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul
-- name    : NumberField.exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/af342cc9-1c97-5a87-a89e-0eec40546ebc
-- title:
--   The T-unit lattice: discreteness, product formula, torsion kernel
-- statement:
--   Let $K$ be a number field and let $T$ be a finite set of height-one primes of $\mathcal{O}_K$. Fix the enumerations of the infinite places of $K$ by `Fintype.equivFin` and of the elements of $T$ by `T.equivFin`. The assertion is that there exist an additive subgroup $\Lambda$ of $(\mathrm{Fin}\,r \to \mathbb{R}) \times (\mathrm{Fin}\,d \to \mathbb{Z})$, where $r$ is the number of infinite places and $d = |T|$, and a map $\mathrm{Log} : K^\times \to (\mathrm{Fin}\,r \to \mathbb{R}) \times (\mathrm{Fin}\,d \to \mathbb{Z})$ with the following five properties. First, $\mathrm{Log}$ is given by the explicit formula whose $i$-th real coordinate is $m_{w_i}\log w_i(u)$, with $w_i$ the $i$-th infinite place and $m_{w_i}$ its multiplicity `mult`, and whose $j$-th integral coordinate is $\mathrm{Multiplicative.toAdd}$ of $v_j$'s `valuationOfNeZero` at $u$, for $v_j$ the $j$-th prime of $T$. Second, $\mathrm{Log}(uu') = \mathrm{Log}(u) + \mathrm{Log}(u')$ for all $u,u' \in K^\times$. Third, $\Lambda$ consists exactly of the vectors $\mathrm{Log}(u)$ for those $u \in K^\times$ whose `valuationOfNeZero` equals $1$ at every height-one prime not in $T$. Fourth, $\Lambda$ carries the discrete topology as a subspace. Fifth, every $\gamma \in \Lambda$ satisfies $\sum_i \gamma_1(i) = \sum_j \bigl(-\log \mathrm{absNorm}(v_j)\bigr)\,\gamma_2(j)$. Finally, for $u \in K^\times$ with trivial `valuationOfNeZero` outside $T$, one has $\mathrm{Log}(u) = 0$ if and only if $u$ is the image in $K$ of an element of `NumberField.Units.torsion K`.
--
--   This packages the elementary half of Dirichlet's $S$-unit theorem — discreteness of the logarithmic image of the $T$-units and Kronecker's characterisation of its kernel as the roots of unity — together with the product formula in logarithmic form, the latter appearing as the single linear relation satisfied by all of $\Lambda$. It is used in the idelic and automorphic computations of the development, where sums over Hecke orbits are controlled by the lattice of $T$-units and by the normalised ideal norms $\mathrm{absNorm}(v_j)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul
    (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (Λ : AddSubgroup ((Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)))
      (Log : Kˣ → (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)),
      (∀ u : Kˣ, Log u =
        (fun i => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) *
            Real.log (((Fintype.equivFin (InfinitePlace K)).symm i) (u : K)),
          fun j => Multiplicative.toAdd ((T.equivFin.symm j).1.valuationOfNeZero u))) ∧
      (∀ u u' : Kˣ, Log (u * u') = Log u + Log u') ∧
      (∀ γ, γ ∈ Λ ↔ ∃ u : Kˣ,
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero u = 1) ∧ Log u = γ) ∧
      DiscreteTopology Λ ∧
      (∀ γ ∈ Λ, ∑ i, γ.1 i =
        ∑ j, -Real.log (Ideal.absNorm (T.equivFin.symm j).1.asIdeal : ℝ) * (γ.2 j : ℝ)) ∧
      (∀ u : Kˣ, (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero u = 1) →
        (Log u = 0 ↔ ∃ ζ : (𝓞 K)ˣ, ζ ∈ NumberField.Units.torsion K ∧ ((ζ : 𝓞 K) : K) = (u : K))) := by sorry
