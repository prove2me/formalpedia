-- Prove2me | Theorems.Thm_GlobalTheory_SplitSep_exists_sep
-- name    : GlobalTheory.SplitSep.exists_sep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:22:10.178995+00:00
-- url     : https://prove2.me/theorems/3c807ad6-0f44-4b3c-bb42-ba17af5b59f3
-- title:
--   Split Sep: exists sep
-- statement:
--   The Split Sep construction uses the exists sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsIntegerUnitSplitPlaceConjugatePrime.lean#L30-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsIntegerUnitSplitPlaceConjugatePrime.lean#L30-L118

import Mathlib
import Definitions.Def_ReciprocityTheory_Automorphisms_Unitary
import Definitions.Def_ReciprocityTheory_Automorphisms_PlaceA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
noncomputable section
open GlobalTheory GlobalTheory.SplitSep
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
local notation3 "cc" => IsCMField.complexConj L
variable (L)

theorem GlobalTheory.SplitSep.exists_sep (s : ReciprocityTheory.Aut.SplitPlace L) :
    ∃ e : 𝓞 L, Valued.v (s.i (e : L)) = 1 ∧
      Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 := by sorry
