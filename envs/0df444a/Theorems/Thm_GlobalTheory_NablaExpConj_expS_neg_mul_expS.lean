-- Prove2me | Theorems.Thm_GlobalTheory_NablaExpConj_expS_neg_mul_expS
-- name    : GlobalTheory.NablaExpConj.expS_neg_mul_expS
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:39:11.132177+00:00
-- url     : https://prove2.me/theorems/6393ee87-c911-4138-a379-07e7cfd6f1f9
-- title:
--   Nabla Exp Conj: exp S neg mul exp S
-- statement:
--   The Nabla Exp Conj construction uses the exp S neg mul exp S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExpSNegMulExpS.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExpSNegMulExpS.lean#L93-L96

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.NablaExpConj
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem GlobalTheory.NablaExpConj.expS_neg_mul_expS {n : ℕ} {g : PS k n d} (hg : constantCoeff g = 0) :
    FB.expS k (-g) * FB.expS k g = 1 := by sorry
