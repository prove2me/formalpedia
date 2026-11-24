-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Pair_smooth_strHom
-- name    : GlobalTheory.SecGlue.Pair.smooth_strHom
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:49:56.486478+00:00
-- url     : https://prove2.me/theorems/cd6248a1-3a9d-4b94-81a5-5726e6f9db7f
-- title:
--   Pair: smooth str Hom
-- statement:
--   The Pair construction uses the smooth str Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquareZeroLiftBasicOpenPairAgree.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquareZeroLiftBasicOpenPairAgree.lean#L60-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquareZeroLiftBasicOpenPairAgree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Pair

theorem GlobalTheory.SecGlue.Pair.smooth_strHom {R : Type} [CommRing R] (X : Over (Sp R)) [Smooth X.hom] {V : X.left.Opens}
    (hV : IsAffineOpen V) : (strHom X V).Smooth := by sorry
