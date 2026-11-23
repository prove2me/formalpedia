-- Prove2me | Theorems.Thm_GlobalTheory_GaugeAdjoint_hasSubst_pts
-- name    : GlobalTheory.GaugeAdjoint.hasSubst_pts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:57.824921+00:00
-- url     : https://prove2.me/theorems/33d91c9f-ff32-4340-9b16-0cb8be3c1c49
-- title:
--   Gauge Adjoint: has Subst pts
-- statement:
--   The Gauge Adjoint construction uses the has Subst pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ConstantCoeffEv.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ConstantCoeffEv.lean#L16-L17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.GaugeAdjoint
open GlobalTheory.FormalCalc GlobalTheory.IntSeries
variable {k : Type} [CommRing k] {d m n p : ℕ}

theorem GlobalTheory.GaugeAdjoint.hasSubst_pts {a : Fin m → Pt k n d} (ha : ∀ j i, constantCoeff (a j i) = 0) :
    HasSubst (fun q : Fin m × Fin d => a q.1 q.2) := by sorry
