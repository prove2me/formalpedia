-- Prove2me | Theorems.Thm_GlobalTheory_T_cmField_adele_split_place_support_integral
-- name    : GlobalTheory.T.cmField_adele_split_place_support_integral
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:28:48.128017+00:00
-- url     : https://prove2.me/theorems/46dc76c3-500b-4f41-9fd1-21429d4f04fe
-- title:
--   T: cm Field adele split place support integral
-- statement:
--   The T construction uses the cm Field adele split place support integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CmFieldAdeleSplitPlaceSupportIntegralStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CmFieldAdeleSplitPlaceSupportIntegralStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegral
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegralStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.cmField_adele_split_place_support_integral : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (e : 𝓞 L), Valued.v (s.i (e : L)) = 1 → Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 → ∀ z : ReciprocityTheory.Aut.AL L, (∀ w, w ≠ s.v → ReciprocityTheory.Aut.compAt L w z = 0) → Valued.v (s.proj z) ≤ 1 → Valued.v (s.proj (ReciprocityTheory.Aut.conjAL L z)) ≤ 1 → z ∈ ReciprocityTheory.Aut.ALint L := by sorry
