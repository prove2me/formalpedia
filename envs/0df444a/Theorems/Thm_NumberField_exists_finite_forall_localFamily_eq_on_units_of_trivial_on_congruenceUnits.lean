-- Prove2me | Theorems.Thm_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits
-- name    : NumberField.exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/70cd7d8b-547b-5ed4-9aec-8f0125d83a0d
-- title:
--   Finitely many unit-character restrictions at bounded level
-- statement:
--   Let $K$ be a number field, $SK$ a finite set of finite places of $K$ (nonzero primes of $\mathcal{O}_K$), and $N$ a nonzero ideal of $\mathcal{O}_K$. The assertion is that there exist a natural number $n$ and a finite list $\rho_1,\dots,\rho_n$ (indexed by `Fin n`) of families $\rho_r = (\rho_{r,v})_v$, where for each finite place $v$ the component $\rho_{r,v}$ is a group homomorphism from the unit group of the completion $K_v$ to $\mathbb{C}^\times$ (no continuity is required), with the following property. Let $\chi = (\chi_v)_v$ be any family of group homomorphisms $K_v^\times \to \mathbb{C}^\times$ such that for every $v \in SK$ and every $t \in K_v^\times$ with both $t$ and $t^{-1}$ lying in the valuation ring of $K_v$ and with $v(t-1) \le q_v^{-e_v}$, where $e_v$ denotes the multiplicity of $v$ in the factorisation of $N$ (this bound being `idealBound (𝓞 K) N v`, i.e. $t \equiv 1$ modulo $v^{e_v}$), one has $\chi_v(t) = 1$. Then there is an index $r$ such that for every $v \in SK$ and every $u$ with $u$ and $u^{-1}$ in the valuation ring of $K_v$ one has $\chi_v(u) = \rho_{r,v}(u)$.
--
--   This is the finiteness statement that characters of the local unit groups $\mathcal{O}_v^\times$ trivial on the congruence subgroup cut out by $N$ form a finite set at each place, uniformly over a finite set $SK$ of places: the list $\rho_1,\dots,\rho_n$ exhausts the possible simultaneous restrictions to the $\mathcal{O}_v^\times$, $v \in SK$. It is used in the analysis of the local components of adelic automorphic forms of principal level, where it supplies finitely many candidate unramified-character types.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits.lean

import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem NumberField.exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits
    (K : Type) [Field K] [NumberField K]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) :
    ∃ (n : ℕ) (ρs : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ),
    ∀ (χ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
      (_hχ : ∀ v ∈ SK, ∀ t : (v.adicCompletion K)ˣ, (t : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        Valued.v ((t : v.adicCompletion K) - 1) ≤ idealBound (𝓞 K) N v → χ v t = 1),
    ∃ r : Fin n, ∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        χ v u = ρs r v u := by sorry
