-- Prove2me | Theorems.Thm_GlobalTheory_ResidueExtension_exists_localization
-- name    : GlobalTheory.ResidueExtension.exists_localization
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:21:14.120473+00:00
-- url     : https://prove2.me/theorems/bff3ef31-1f5c-42b5-94a2-75964a969903
-- title:
--   Residue Extension: exists localization
-- statement:
--   The Residue Extension construction uses the exists localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsCompleteDiscreteValuationRingWithResidues.lean#L21-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsCompleteDiscreteValuationRingWithResidues.lean#L21-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsCompleteDiscreteValuationRingWithResidues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory
open GlobalTheory.ResidueExtension
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω]

theorem GlobalTheory.ResidueExtension.exists_localization {A : Type} [CommRing A] [IsNoetherianRing A] (i : O →+* A)
    (ψ : A →+* Ω) {π : O} (hπ : Irreducible π) (hker : RingHom.ker ψ = Ideal.span {i π})
    (hreg : ∀ x, i π * x = 0 → x = 0) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B)
      (j : O →+* B) (r' : B →+* Ω), Function.Injective j ∧ r'.comp j = ψ.comp i ∧
      RingHom.ker r' = maximalIdeal B ∧ Set.range ψ ⊆ Set.range r' := by sorry
