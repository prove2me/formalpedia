-- Prove2me | Theorems.Thm_GlobalTheory_T_anisotropicFiniteLengths_of_shortLatticeVector
-- name    : GlobalTheory.T.anisotropicFiniteLengths_of_shortLatticeVector
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:26:43.374589+00:00
-- url     : https://prove2.me/theorems/b8a040f2-65f2-4d7c-aa6c-7bf85db2ee5f
-- title:
--   T: anisotropic Finite Lengths of short Lattice Vector
-- statement:
--   The T construction uses the anisotropic Finite Lengths of short Lattice Vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AnisotropicFiniteLengthsOfShortLatticeVectorStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AnisotropicFiniteLengthsOfShortLatticeVectorStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVector
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVectorStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.anisotropicFiniteLengths_of_shortLatticeVector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ShortSmall E → AnisoSmall E := by sorry
