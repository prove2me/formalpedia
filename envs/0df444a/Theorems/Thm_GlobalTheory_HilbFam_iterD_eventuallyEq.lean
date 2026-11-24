-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_iterD_eventuallyEq
-- name    : GlobalTheory.HilbFam.iterD_eventuallyEq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:20:57.524433+00:00
-- url     : https://prove2.me/theorems/390fae9f-0b0e-4800-b231-570f1949812f
-- title:
--   Hilb Fam: iter D eventually Eq
-- statement:
--   The Hilb Fam construction uses the iter D eventually Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IterDEqOfEventuallyEq.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IterDEqOfEventuallyEq.lean#L11-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IterDEqOfEventuallyEq
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

theorem GlobalTheory.HilbFam.iterD_eventuallyEq (I : Type) [Fintype I] [DecidableEq I] (u : List I)
    (f g : (I → ℂ) → ℂ) (z : I → ℂ) (h : f =ᶠ[nhds z] g) :
    iterD u f =ᶠ[nhds z] iterD u g := by sorry
