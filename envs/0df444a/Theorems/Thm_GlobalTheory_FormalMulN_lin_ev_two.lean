-- Prove2me | Theorems.Thm_GlobalTheory_FormalMulN_lin_ev_two
-- name    : GlobalTheory.FormalMulN.lin_ev_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:17.184848+00:00
-- url     : https://prove2.me/theorems/c563a943-f03c-4fa3-a551-7279760d2d6d
-- title:
--   Formal Mul N: lin ev two
-- statement:
--   The Formal Mul N construction uses the lin ev two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/FormalGroupLawCompMulNZero.lean#L120-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/FormalGroupLawCompMulNZero.lean#L120-L128

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

theorem GlobalTheory.FormalMulN.lin_ev_two {x y : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (f : PS R 2 d) (s : Fin n × Fin d) :
    coeff (Finsupp.single s 1) (ev ![x, y] f) =
      ∑ l, coeff (Finsupp.single ((0 : Fin 2), l) 1) f * coeff (Finsupp.single s 1) (x l) +
      ∑ l, coeff (Finsupp.single ((1 : Fin 2), l) 1) f * coeff (Finsupp.single s 1) (y l) := by sorry
