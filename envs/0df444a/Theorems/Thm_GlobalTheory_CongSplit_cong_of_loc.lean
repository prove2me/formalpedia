-- Prove2me | Theorems.Thm_GlobalTheory_CongSplit_cong_of_loc
-- name    : GlobalTheory.CongSplit.cong_of_loc
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:25:22.646063+00:00
-- url     : https://prove2.me/theorems/d1bea333-6a8d-4838-ac4c-c45286ef5c0f
-- title:
--   Cong Split: cong of loc
-- statement:
--   The Cong Split construction uses the cong of loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CongOfLoc.lean#L21-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CongOfLoc.lean#L21-L77

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CongOfLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
noncomputable section
open GlobalTheory GlobalTheory.CongSplit

theorem GlobalTheory.CongSplit.cong_of_loc : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (N : ℕ), 0 < N →
    ∀ x : GAf L n, TrivOutside {s.v} x →
    (∀ i j, Valued.v (((s.loc n x : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j -
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j) ≤
      Valued.v ((N : s.v.adicCompletion (NumberField.maximalRealSubfield L)))) →
    (∀ i j, Valued.v (((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j -
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j) ≤
      Valued.v ((N : s.v.adicCompletion (NumberField.maximalRealSubfield L)))) →
    NG.Cong L n N x := by sorry
