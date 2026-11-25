-- Prove2me | Theorems.Thm_GlobalTheory_NablaExpConj_pderiv_inr_liftX
-- name    : GlobalTheory.NablaExpConj.pderiv_inr_liftX
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:38:50.272839+00:00
-- url     : https://prove2.me/theorems/36274e27-0b36-41bd-b282-77d96b87b051
-- title:
--   Nabla Exp Conj: pderiv inr lift X
-- statement:
--   The Nabla Exp Conj construction uses the pderiv inr lift X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExpSNegMulExpS.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExpSNegMulExpS.lean#L42-L46

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

theorem GlobalTheory.NablaExpConj.pderiv_inr_liftX (f : PS k 1 d) (i : Fin d) : pderiv k (Sum.inr i) (liftX k f) = 0 := by sorry
