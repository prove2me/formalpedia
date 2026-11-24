-- Prove2me | Theorems.Thm_GlobalTheory_FormalMulN_ev_add_pts
-- name    : GlobalTheory.FormalMulN.ev_add_pts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:04.896818+00:00
-- url     : https://prove2.me/theorems/93fa2bf9-4843-4f02-86ac-fd94cbe1d6ff
-- title:
--   Formal Mul N: ev add pts
-- statement:
--   The Formal Mul N construction uses the ev add pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/FormalGroupLawCompMulNZero.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/FormalGroupLawCompMulNZero.lean#L38-L43

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

theorem GlobalTheory.FormalMulN.ev_add_pts {x y : Pt R m d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) {b : Fin m → Pt R n d}
    (hb : ∀ j i, constantCoeff (b j i) = 0) :
    (fun i => ev b (G.add x y i)) = G.add (fun i => ev b (x i)) (fun i => ev b (y i)) := by sorry
