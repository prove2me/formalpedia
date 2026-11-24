-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_isSquare_of_valued_sub_one_lt
-- name    : GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:16:29.864223+00:00
-- url     : https://prove2.me/theorems/c40f8ebb-1cbb-446d-97d9-916fe621cc32
-- title:
--   Local Quad: is Square of valued sub one lt
-- statement:
--   The Local Quad construction uses the is Square of valued sub one lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSquareOfValuedSubOneLt.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSquareOfValuedSubOneLt.lean#L57-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
open NumberField IsDedekindDomain
open scoped Matrix WithZero

theorem GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (h : Valued.v (x - 1) < Valued.v (4 : v.adicCompletion F)) : IsSquare x := by sorry
