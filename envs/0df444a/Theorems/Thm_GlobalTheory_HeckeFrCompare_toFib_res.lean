-- Prove2me | Theorems.Thm_GlobalTheory_HeckeFrCompare_toFib_res
-- name    : GlobalTheory.HeckeFrCompare.toFib_res
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:45:31.697673+00:00
-- url     : https://prove2.me/theorems/c36132cf-2b4e-4597-9d23-7e4ad509bfa0
-- title:
--   Hecke Fr Compare: to Fib res
-- statement:
--   The Hecke Fr Compare construction uses the to Fib res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L113-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L113-L118

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HeckeFrCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {Ω : Type} [CommRing Ω]

theorem GlobalTheory.HeckeFrCompare.toFib_res (x : Sp Ω ⟶ Xo.X) {T T' : Scheme.{0}} {t : T ⟶ Sp Ω} {t' : T' ⟶ Sp Ω} (q : T' ⟶ T)
    (hq : q ≫ t = t') (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    toFib x t' (res x q hq ≫ a) = q ≫ toFib x t a := by sorry
