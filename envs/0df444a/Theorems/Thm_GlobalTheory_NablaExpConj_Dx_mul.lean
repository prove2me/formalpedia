-- Prove2me | Theorems.Thm_GlobalTheory_NablaExpConj_Dx_mul
-- name    : GlobalTheory.NablaExpConj.Dx_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:58.973823+00:00
-- url     : https://prove2.me/theorems/cc141f9d-2da3-418e-80c0-6a670acf9bc8
-- title:
--   Nabla Exp Conj: Dx mul
-- statement:
--   The Nabla Exp Conj construction uses the Dx mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExpSNegMulExpS.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExpSNegMulExpS.lean#L60-L64

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
omit [Algebra ℚ k]

theorem GlobalTheory.NablaExpConj.Dx_mul (B : FB R d O) (u : Fin d → k) (f G : AA k d) :
    Dx k B u (f * G) = Dx k B u f * G + f * Dx k B u G := by sorry
