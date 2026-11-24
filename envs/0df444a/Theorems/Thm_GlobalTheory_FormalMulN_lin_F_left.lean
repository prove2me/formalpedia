-- Prove2me | Theorems.Thm_GlobalTheory_FormalMulN_lin_F_left
-- name    : GlobalTheory.FormalMulN.lin_F_left
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:36:13.078573+00:00
-- url     : https://prove2.me/theorems/b2818c01-9f81-439a-bc16-231385c3526e
-- title:
--   Formal Mul N: lin F left
-- statement:
--   The Formal Mul N construction uses the lin F left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/FormalGroupLawCompMulNZero.lean#L169-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/FormalGroupLawCompMulNZero.lean#L169-L174

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

theorem GlobalTheory.FormalMulN.lin_F_left (i l : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), l) 1) (G.F i) = if i = l then 1 else 0 := by sorry
