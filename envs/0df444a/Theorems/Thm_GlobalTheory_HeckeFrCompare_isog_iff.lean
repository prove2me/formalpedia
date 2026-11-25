-- Prove2me | Theorems.Thm_GlobalTheory_HeckeFrCompare_isog_iff
-- name    : GlobalTheory.HeckeFrCompare.isog_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:45:54.550815+00:00
-- url     : https://prove2.me/theorems/30ae3b82-5373-45bf-bd43-9e73792feb01
-- title:
--   Hecke Fr Compare: isog iff
-- statement:
--   The Hecke Fr Compare construction uses the isog iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L306-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L306-L341

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

theorem GlobalTheory.HeckeFrCompare.isog_iff {Ω : Type} [Field Ω] [IsAlgClosed Ω] {p : ℕ} (hp : p.Coprime l.M') (x x' : Sp Ω ⟶ Xo.X)
    (C : Subgroup (Over.mk x ⟶ Xo.univ.t.G)) (ψ : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x') :
    (∃ ψp, IsHkIsog p x x' C ψ ψp) ↔ IsHeckeIsog p C (conj x x' ψ) := by sorry
