-- Prove2me | Theorems.Thm_GlobalTheory_SW_ShortStep_den_inv_smul
-- name    : GlobalTheory.SW.ShortStep.den_inv_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:09.695086+00:00
-- url     : https://prove2.me/theorems/4e047c98-4fec-4d63-b02e-fd9b5502c4ae
-- title:
--   Short Step: den inv smul
-- statement:
--   The Short Step construction uses the den inv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ShortIsotropicVectorsExistenceSuccOfVeryShortSte.lean#L187-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ShortIsotropicVectorsExistenceSuccOfVeryShortSte.lean#L187-L191

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSte
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ShortStep
open MinkowskiProductBounds
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
omit [IsCMField E]

theorem GlobalTheory.SW.ShortStep.den_inv_smul {α β : Type} {a c : ℕ} (hc : 0 < c) {A : Matrix α β E} (hA : Den a A) :
    Den (a * c) ((c : E)⁻¹ • A) := by sorry
