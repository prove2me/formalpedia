-- Prove2me | Theorems.Thm_GlobalTheory_T_covolume_fractionalIdealRealLatticeImage
-- name    : GlobalTheory.T.covolume_fractionalIdealRealLatticeImage
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:31:57.170403+00:00
-- url     : https://prove2.me/theorems/2636a1fb-d64e-44ed-a5e0-1d41fdc4d8d5
-- title:
--   T: covolume fractional Ideal Real Lattice Image
-- statement:
--   The T construction uses the covolume fractional Ideal Real Lattice Image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovolumeFractionalIdealRealLatticeImageStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovolumeFractionalIdealRealLatticeImageStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovolumeFractionalIdealRealLatticeImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovolumeFractionalIdealRealLatticeImageStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.covolume_fractionalIdealRealLatticeImage : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → ∀ [DiscreteTopology (latOf N)] [IsZLattice ℝ (latOf N)], ZLattice.covolume (latOf N) = covol N := by sorry
