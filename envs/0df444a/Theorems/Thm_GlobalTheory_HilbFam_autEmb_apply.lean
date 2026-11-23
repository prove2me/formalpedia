-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_autEmb_apply
-- name    : GlobalTheory.HilbFam.autEmb_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:11:02.058886+00:00
-- url     : https://prove2.me/theorems/17a787b9-4f02-438a-bf26-1f244fb1d575
-- title:
--   Hilb Fam: aut Emb apply
-- statement:
--   The Hilb Fam construction uses the aut Emb apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AutEmbInjective.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AutEmbInjective.lean#L13-L15

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AutEmbInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam

theorem GlobalTheory.HilbFam.autEmb_apply {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ) (i : Emb F) (y : F) :
    ((autEmb g i y : ℝ) : ℂ) = g ((i y : ℝ) : ℂ) := by sorry
