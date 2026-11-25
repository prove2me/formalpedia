-- Prove2me | Theorems.Thm_GlobalTheory_NablaExpConj_liftX_hasSubst
-- name    : GlobalTheory.NablaExpConj.liftX_hasSubst
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:36:56.961803+00:00
-- url     : https://prove2.me/theorems/adc18569-d860-4617-8eba-505654ebf060
-- title:
--   Nabla Exp Conj: lift X has Subst
-- statement:
--   The Nabla Exp Conj construction uses the lift X has Subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExpSNegMulExpS.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExpSNegMulExpS.lean#L19-L20

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

theorem GlobalTheory.NablaExpConj.liftX_hasSubst : HasSubst (fun p : Fin 1 × Fin d => (X (Sum.inl p.2) : AA k d)) := by sorry
