-- Prove2me | Theorems.Thm_NumberField_SUnits_exists_sLevel_forall_sUnitsRep_map_val_eq_pow
-- name    : NumberField.SUnits.exists_sLevel_forall_sUnitsRep_map_val_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/bb14276b-45a5-54da-82f9-e31c9338362e
-- title:
--   An S-level making S-units of F₁ into p-th powers
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes containing $p$ (the element `pPrime p` of `Nat.Primes`). Let $S_{\mathbb Q}$ be a finite set of height-one primes of $\mathcal O_{\mathbb Q}$ whose underlying set is [`NumberField.placesOverPrimes ℚ S`](def/M4aHerbrand_SIdeleClassGroup.html#L313), i.e. the set of those primes $w$ with $q \in w$ for some $q \in S$. Let $F_1$ be an intermediate field of $\mathbb Q \subseteq \overline{\mathbb Q}$ which is a number field and is Galois over $\mathbb Q$, and assume $F_1$ is unramified outside $S$ in the sense of `IsUnramifiedOutside`: $F_1/\mathbb Q$ is finite and, for every rational prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, the image in $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ (inside its decomposition subgroup) lies in the fixing subgroup of $F_1$. The assertion is that there is an intermediate field $F_1' \supseteq F_1$ of $\overline{\mathbb Q}/\mathbb Q$ which is finite over $\mathbb Q$, Galois over $\mathbb Q$ and unramified outside $S$ in the same sense, with the following property: for every intermediate field $F_3$ that is a number field with $F_1' \le F_3$, and every element $e$ of the $\mathbb Z$-module underlying the Galois representation `sUnitsRep ℚ ↥F₁ Sℚ`, namely the submodule of $\mathrm{Additive}(F_1^\times)$ attached to the subgroup `sUnits ℚ ↥F₁ Sℚ` of $S_{\mathbb Q}$-units, there is an element $e'$ of `sUnitsRep ℚ ↥F₃ Sℚ` such that, after transporting both to units of $\overline{\mathbb Q}$ along the structure maps (via [`NumberField.SUnits.val`](def/NumberField_SUnitsModule.html#L78) and `Units.map`), the image of $e$ equals the $p$-th power of the image of $e'$.
--
--   This is the Kummer step in the construction of a cofinal system of $S$-levels: passing to a suitable finite Galois extension unramified outside $S$ makes all $S$-units of $F_1$ into $p$-th powers of $S$-units higher up, with the $p$-th root field still unramified outside $S$ because $p \in S$. It is used in [`NumberField.SUnits.exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero`](thm.html#NumberField.SUnits.exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero), where the resulting divisibility by $p$ annihilates $\operatorname{Ext}^1_{\mathbb Z}$ against $p$-torsion modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SUnits_exists_sLevel_forall_sUnitsRep_map_val_eq_pow.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_GroupCohomology_ContinuousUnramified

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField
open IsDedekindDomain ExtCitation

theorem NumberField.SUnits.exists_sLevel_forall_sUnitsRep_map_val_eq_pow
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₁] [IsGalois ℚ ↥F₁] (hF₁ : F₁.IsUnramifiedOutside S) :
    ∃ F₁' : IntermediateField ℚ (AlgebraicClosure ℚ), F₁ ≤ F₁' ∧ FiniteDimensional ℚ ↥F₁' ∧ IsGalois ℚ ↥F₁' ∧ F₁'.IsUnramifiedOutside S ∧
      ∀ (F₃ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₃] (_ : F₁' ≤ F₃)
        (e : NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ),
        ∃ e' : NumberField.SUnits.sUnitsRep ℚ ↥F₃ Sℚ,
          Units.map (algebraMap ↥F₁ (AlgebraicClosure ℚ) : ↥F₁ →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F₁ Sℚ e) =
            (Units.map (algebraMap ↥F₃ (AlgebraicClosure ℚ) : ↥F₃ →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F₃ Sℚ e')) ^ p := by sorry
