-- Prove2me | Theorems.Thm_GlobalTheory_isDiscreteValuationRing_of_etale_of_isLocalHom
-- name    : GlobalTheory.isDiscreteValuationRing_of_etale_of_isLocalHom
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:47:11.433018+00:00
-- url     : https://prove2.me/theorems/29c35379-32f9-57e2-a800-847429bb3e36
-- title:
--   Global Theory: is Discrete Valuation Ring of etale of is Local Hom
-- statement:
--   The Global Theory construction uses the is Discrete Valuation Ring of etale of is Local Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L284-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L284-L307

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem GlobalTheory.isDiscreteValuationRing_of_etale_of_isLocalHom (V V' : Type*) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing V'] [IsLocalRing V'] [Algebra V V']
    [IsLocalHom (algebraMap V V')] [Algebra.Etale V V'] :
    ∃ (_ : IsDomain V') (_ : IsDiscreteValuationRing V'),
      (maximalIdeal V).map (algebraMap V V') = maximalIdeal V' ∧
      Module.FaithfullyFlat V V' ∧
      Module.Finite (ResidueField V) (ResidueField V') ∧
      Algebra.IsSeparable (ResidueField V) (ResidueField V') ∧
      ∃ (_ : Algebra (FractionRing V) (FractionRing V'))
        (_ : IsScalarTower V (FractionRing V) (FractionRing V')),
        Module.Finite (FractionRing V) (FractionRing V') ∧
        Algebra.IsSeparable (FractionRing V) (FractionRing V') := by sorry
