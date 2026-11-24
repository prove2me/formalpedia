-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_integer_unit_split_place_conjugate_prime
-- name    : GlobalTheory.T.exists_integer_unit_split_place_conjugate_prime
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:35:20.426527+00:00
-- url     : https://prove2.me/theorems/bfb1d8ce-1aeb-4745-b644-9561e5645bda
-- title:
--   T: exists integer unit split place conjugate prime
-- statement:
--   The T construction uses the exists integer unit split place conjugate prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsIntegerUnitSplitPlaceConjugatePrimeStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsIntegerUnitSplitPlaceConjugatePrimeStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrime
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrimeStatement
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

theorem GlobalTheory.T.exists_integer_unit_split_place_conjugate_prime : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L), ∃ e : 𝓞 L, Valued.v (s.i (e : L)) = 1 ∧ Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 := by sorry
