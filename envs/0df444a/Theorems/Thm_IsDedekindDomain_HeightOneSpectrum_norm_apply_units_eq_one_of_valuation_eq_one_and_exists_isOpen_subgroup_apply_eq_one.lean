-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_norm_apply_units_eq_one_of_valuation_eq_one_and_exists_isOpen_subgroup_apply_eq_one
-- name    : IsDedekindDomain.HeightOneSpectrum.norm_apply_units_eq_one_of_valuation_eq_one_and_exists_isOpen_subgroup_apply_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/3e6cdf85-76f8-58cd-b2b8-4e1f2e01ac93
-- title:
--   Continuous characters of Kᵥ^× are unitary and locally trivial
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal{O}_K$, and let $v$ be a point of the height-one spectrum of $\mathcal{O}_K$, i.e. a nonzero prime ideal; write $K_v$ for the associated adic completion, equipped with its canonical valued structure, and $K_v^\times$ for its unit group with the induced topology. Let $\chi : K_v^\times \to \mathbb{C}^\times$ be a homomorphism of monoids such that the composite $t \mapsto \chi(t)$, viewed as a map $K_v^\times \to \mathbb{C}$, is continuous. The conclusion is a conjunction of two assertions. First, for every $t \in K_v^\times$ whose valuation $\mathrm{v}(t)$ (the canonical valuation of the valued field $K_v$) equals $1$, the complex absolute value $\lVert \chi(t) \rVert$ equals $1$; that is, $\chi$ takes values of modulus one on the units of the valuation ring. Second, there exists a subgroup $U \le K_v^\times$ whose underlying set is open in $K_v^\times$ and such that $\chi(t) = 1$ for every $t \in U$. Note that continuity is imposed only on the $\mathbb{C}$-valued map, and no normalisation or quasi-character growth condition is assumed.
--
--   These are the two standard local facts about continuous quasi-characters of a non-archimedean local field: unitarity on the compact subgroup of valuation-ring units, and triviality on a congruence subgroup (existence of a conductor). They are used in the treatment of automorphic forms, where local components of an idele class character must be shown to be constant on subgroups of finite index, in the two orbital-integral/class-sum identities that cite this result.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_norm_apply_units_eq_one_of_valuation_eq_one_and_exists_isOpen_subgroup_apply_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem IsDedekindDomain.HeightOneSpectrum.norm_apply_units_eq_one_of_valuation_eq_one_and_exists_isOpen_subgroup_apply_eq_one
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : Continuous fun t : (v.adicCompletion K)ˣ => ((χ t : ℂˣ) : ℂ)) :
    (∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 → ‖((χ t : ℂˣ) : ℂ)‖ = 1) ∧
    ∃ U : Subgroup (v.adicCompletion K)ˣ, IsOpen (U : Set (v.adicCompletion K)ˣ) ∧ ∀ t ∈ U, χ t = 1 := by sorry
