-- Prove2me | Theorems.Thm_GlobalTheory_FormalMulN_formalGroupLaw_comp_mulN_zero
-- name    : GlobalTheory.FormalMulN.formalGroupLaw_comp_mulN_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:36:57.044874+00:00
-- url     : https://prove2.me/theorems/01847a80-45b9-4711-a882-65c806623738
-- title:
--   Formal Mul N: formal Group Law comp mul N zero
-- statement:
--   The Formal Mul N construction uses the formal Group Law comp mul N zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/FormalGroupLawCompMulNZero.lean#L93-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/FormalGroupLawCompMulNZero.lean#L93-L95

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalMulN
open GlobalTheory.GaugeAdjoint
variable {R : Type} [CommRing R] {d m n : ℕ} (G : FGLaw R d)

theorem GlobalTheory.FormalMulN.formalGroupLaw_comp_mulN_zero {x : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0) :
    comp1 (mulN G 0) x = 0 := by sorry
