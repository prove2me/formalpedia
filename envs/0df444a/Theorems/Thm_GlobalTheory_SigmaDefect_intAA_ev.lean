-- Prove2me | Theorems.Thm_GlobalTheory_SigmaDefect_intAA_ev
-- name    : GlobalTheory.SigmaDefect.intAA_ev
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:14:41.538829+00:00
-- url     : https://prove2.me/theorems/2ce73bf4-7765-49f1-9061-8133b1f95ddc
-- title:
--   Sigma Defect: int AA ev
-- statement:
--   The Sigma Defect construction uses the int AA ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/SigmaDefectEvalPhaseOne.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/SigmaDefectEvalPhaseOne.lean#L78-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_SigmaDefectEvalPhaseOne
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.SigmaDefect
open GlobalTheory.QuadDeriv GlobalTheory.IntSeries
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
omit [Algebra ℚ k]

theorem GlobalTheory.SigmaDefect.intAA_ev {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j))
    (hai : ∀ j i, IntAA (R := R) k (a j i)) {f : PS k m d} (hf : IntAA (R := R) k f) :
    IntAA (R := R) k (ev a f) := by sorry
