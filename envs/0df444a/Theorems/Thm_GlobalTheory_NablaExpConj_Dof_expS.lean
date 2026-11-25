-- Prove2me | Theorems.Thm_GlobalTheory_NablaExpConj_Dof_expS
-- name    : GlobalTheory.NablaExpConj.Dof_expS
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:36:46.356528+00:00
-- url     : https://prove2.me/theorems/d07c18be-80f0-4cc9-8ac6-428fcd020d3a
-- title:
--   Nabla Exp Conj: Dof exp S
-- statement:
--   The Nabla Exp Conj construction uses the Dof exp S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExpSNegMulExpS.lean#L83-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExpSNegMulExpS.lean#L83-L91

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

theorem GlobalTheory.NablaExpConj.Dof_expS (F : Fin d → PS k 2 d) (u : Fin d → k) {g : PS k 1 d}
    (hg : constantCoeff g = 0) : Dof F u (FB.expS k g) = FB.expS k g * Dof F u g := by sorry
