-- Prove2me | Theorems.Thm_GlobalTheory_NablaExpConj_liftX_mul
-- name    : GlobalTheory.NablaExpConj.liftX_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:36:45.438462+00:00
-- url     : https://prove2.me/theorems/cd7d5ee2-09ab-4439-a9d2-a6144becb185
-- title:
--   Nabla Exp Conj: lift X mul
-- statement:
--   The Nabla Exp Conj construction uses the lift X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExpSNegMulExpS.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExpSNegMulExpS.lean#L25-L26

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
variable (k : Type) [CommRing k]

theorem GlobalTheory.NablaExpConj.liftX_mul (f g : PS k 1 d) : liftX k (f * g) = liftX k f * liftX k g := by sorry
