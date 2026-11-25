-- Prove2me | Theorems.Thm_GlobalTheory_HeckeFrCompare_lie_iff
-- name    : GlobalTheory.HeckeFrCompare.lie_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T15:08:38.733235+00:00
-- url     : https://prove2.me/theorems/1bcf0c30-cf8c-50b6-bc7f-e4fd07c832c5
-- title:
--   Hecke Fr Compare: lie iff
-- statement:
--   The Hecke Fr Compare construction uses the lie iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L351-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L351-L372

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

theorem GlobalTheory.HeckeFrCompare.lie_iff {Ω : Type} [Field Ω] {p : ℕ} (hp : (p : Ω) ≠ 0) {x x' : Sp Ω ⟶ Xo.X}
    (ψ : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x')
    (v w : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left) :
    (IsTanAt x v ∧ IsTanAt x' w ∧ IsLieImageH p ψ v w) ↔ IsLieImg p (conj x x' ψ) v w := by sorry
