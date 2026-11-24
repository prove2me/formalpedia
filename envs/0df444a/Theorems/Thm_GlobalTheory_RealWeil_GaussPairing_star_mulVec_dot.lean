-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_GaussPairing_star_mulVec_dot
-- name    : GlobalTheory.RealWeil.GaussPairing.star_mulVec_dot
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:15:07.133886+00:00
-- url     : https://prove2.me/theorems/667b6c2f-9f73-42d4-a2af-141c3b9b674c
-- title:
--   Gauss Pairing: star mul Vec dot
-- statement:
--   The Gauss Pairing construction uses the star mul Vec dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianPairingUnitaryGroupTwoThree.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianPairingUnitaryGroupTwoThree.lean#L33-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HalfAddSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralComplexGaussianPosDefHermitianPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingOfNormSqEqSumComplexCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.GaussPairing
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type} [Fintype ι]

theorem GlobalTheory.RealWeil.GaussPairing.star_mulVec_dot (g : Matrix ι ι ℂ) (z w : ι → ℂ) :
    star (g *ᵥ z) ⬝ᵥ w = star z ⬝ᵥ gᴴ *ᵥ w := by sorry
