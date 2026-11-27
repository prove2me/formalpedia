-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_EndBlock_isEnd_block_raw
-- name    : GlobalTheory.RowLaw.EndBlock.isEnd_block_raw
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-27T06:08:19.626634+00:00
-- url     : https://prove2.me/theorems/c03999c1-7287-470b-a34b-b4be2a896a2c
-- title:
--   End Block: is End block raw
-- statement:
--   The End Block construction uses the is End block raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeAdjointEndPairElementaryBlock.lean#L153-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeAdjointEndPairElementaryBlock.lean#L153-L202

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeAdjointEndPairElementaryBlock
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.EndBlock
open MvPowerSeries
variable {C : Type} [Field C]
variable {dd : ℕ}
variable {d d' : ℕ} {I I' : Fin 2 → Type} (X : RawChart C d I (Fin dd)) (Z : RawChart C d' I' (Fin 2 × Fin dd))

theorem GlobalTheory.RowLaw.EndBlock.isEnd_block_raw [CharZero C] (V : VF C) (hlg : ∀ x, Z.lg x = inCol x.1 (X.lg x.2))
    (hex : ∀ x, Z.ex x = inCol x.1 (X.ex x.2)) (hh : Z.h = ∑ col, hCol col X.h)
    (hlg0 : ∀ i, constantCoeff (X.lg i) = 0) (hex0 : ∀ i, constantCoeff (X.ex i) = 0)
    (hax : ∀ (g : Fin 2) (e : Fin 2 × Fin dd →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e X.h = 0)
    (r s : Fin 2) (M M' : Matrix (Fin dd) (Fin dd) C) (H : IsEnd X V M M') :
    IsEnd Z V (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = r ∧ y.1 = s then M x.2 y.2 else 0)
      (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = s ∧ y.1 = r then M' x.2 y.2 else 0) := by sorry
