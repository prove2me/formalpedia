-- Prove2me | Theorems.Thm_GlobalTheory_FiniteLengthComplex_nonempty_iso_residue
-- name    : GlobalTheory.FiniteLengthComplex.nonempty_iso_residue
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:01:42.312402+00:00
-- url     : https://prove2.me/theorems/7019b7e9-7219-48cf-b582-302683f20c33
-- title:
--   Finite Length Complex: nonempty iso residue
-- statement:
--   The Finite Length Complex construction uses the nonempty iso residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L29-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing
open GlobalTheory
open GlobalTheory.FiniteLengthComplex
variable {R : Type} [CommRing R]

theorem GlobalTheory.FiniteLengthComplex.nonempty_iso_residue [IsLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] :
    Nonempty (ModuleCat.of R M ≅ ModuleCat.of R (R ⧸ maximalIdeal R)) := by sorry
