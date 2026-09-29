-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_cocyclesTwo_conj_transport_continuousH2SrInflation_eq
-- name    : NumberField.LevelArith.exists_cocyclesTwo_conj_transport_continuousH2SrInflation_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/55670bee-ece9-51b8-9b76-2da1be484748
-- title:
--   Conjugating an inflated level 2-cocycle by σ
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes. Let $L \subseteq \overline{\mathbb{Q}}$ be a finite intermediate extension of $\mathbb{Q}$ which is unramified outside $S$ (for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in $L$'s fixing subgroup $\Gamma_L$), and let $F \supseteq L$ be a further such field, finite and normal over $\mathbb{Q}$ and unramified outside $S$. Let $\sigma$ be a $\mathbb{Q}$-automorphism of $\overline{\mathbb{Q}}$ whose restriction to $L$ is a given $\tau \in \mathrm{Aut}_{\mathbb{Q}}(L)$. Write $E =$ `sUnitsMaxRep S L`, the $\mathbb{Z}[\Gamma_L]$-module of $S$-units cut out by `sUnitsMaxSubmodule` inside $\mathrm{Additive}\,\overline{\mathbb{Q}}^{\times}$, and let $H =$ `continuousH2Sr` be the quotient of the level $2$-cocycles `levelCocyclesSr₂` by the level $2$-coboundaries, with projection $\pi =$ `continuousH2Srπ`. Let $a, a'$ be elements of the $p$-power torsion submodule of $H$, presented by level cocycles $w, w'$ via $a = \pi(w)$, $a' = \pi(w')$, and assume the values are $\sigma$-conjugate: whenever $s, t, s', t' \in \Gamma_L$ satisfy $\sigma^{-1} s \sigma = s'$ and $\sigma^{-1} t \sigma = t'$, the unit underlying $w'(s,t)$ equals $\sigma \cdot$ (the unit underlying $w(s',t')$). Let $U_F$ be the preimage in $\Gamma_L$ of $F$'s fixing subgroup, and let $f$ be a $2$-cocycle of $\Gamma_L/U_F$ with values in the $U_F$-invariants of $E$ such that $a$ is the image of the class of $f$ under `continuousH2SrInflation`. The conclusion is that there exists a $2$-cocycle $f^{\sigma}$ of $\Gamma_L/U_F$ with values in the same invariants such that, for $s, t, s', t' \in \Gamma_L$ with $\sigma^{-1} s \sigma = s'$ and $\sigma^{-1} t \sigma = t'$, the unit underlying $f^{\sigma}(\bar{s}, \bar{t})$ equals $\sigma \cdot$ (the unit underlying $f(\bar{s}', \bar{t}')$), and such that $a'$ is the image of the class of $f^{\sigma}$ under `continuousH2SrInflation`.
--
--   This is the transport under conjugation by a Galois element $\sigma$ of a presentation, by inflation from a finite normal layer $F$, of a $p$-power torsion class in the continuous $S$-ramified second cohomology of $\Gamma_L$ acting on $S$-units: the $\sigma$-conjugate class $a'$ is presented at the same layer by the $\sigma$-conjugate cocycle. It is used in the comparison of local invariants under field isomorphisms, in [`NumberField.LevelArith.apply_eq_apply_of_isBrauerLocalInv_of_algEquiv`](thm.html#NumberField.LevelArith.apply_eq_apply_of_isBrauerLocalInv_of_algEquiv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_cocyclesTwo_conj_transport_continuousH2SrInflation_eq.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain NumberField.LevelArith
open scoped NumberField.LevelArith
open scoped Pointwise

theorem NumberField.LevelArith.exists_cocyclesTwo_conj_transport_continuousH2SrInflation_eq
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (τ : ↥L ≃ₐ[ℚ] ↥L) (hστ : ∀ y : ↥L, σ (y : AlgebraicClosure ℚ) = ((τ y : ↥L) : AlgebraicClosure ℚ))
    (a a' : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ))))
    (w w' : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S (sUnitsMaxRep S L)))
    (ha : (a : (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) = continuousH2Srπ L.fixingSubgroup.subtype S _ w)
    (ha' : (a' : (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) = continuousH2Srπ L.fixingSubgroup.subtype S _ w')
    (hww' : ∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' → σ⁻¹ * (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = t' →
            sUnitsMaxRep.val S L ((w' : ↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L)) (s, t)) =
              σ • sUnitsMaxRep.val S L ((w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L)) (s', t')))
    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (haf : (a : (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)))
        = continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ f)) :
    ∃ fσ : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)),
      (∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' → σ⁻¹ * (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = t' →
        sUnitsMaxRep.val S L ((fσ ((s : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (t : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
          = σ • sUnitsMaxRep.val S L ((f ((s' : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (t' : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)) ∧
      (a' : (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)))
        = continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ fσ) := by sorry
