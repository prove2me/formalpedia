-- Prove2me | Theorems.Thm_GlobalTheory_HeckeFrCompare_pointHom_unique
-- name    : GlobalTheory.HeckeFrCompare.pointHom_unique
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:59:30.087676+00:00
-- url     : https://prove2.me/theorems/ba5755b3-ccb3-5931-89ab-141d691ddf6f
-- title:
--   Hecke Fr Compare: point Hom unique
-- statement:
--   The Hecke Fr Compare construction uses the point Hom unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L299-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L299-L304

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

theorem GlobalTheory.HeckeFrCompare.pointHom_unique {Ω : Type} [Field Ω] [IsAlgClosed Ω] {p : ℕ} {x x' : Sp Ω ⟶ Xo.X}
    {C : Subgroup (Over.mk x ⟶ Xo.univ.t.G)} {ψ : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x'}
    {f g : (Over.mk x ⟶ Xo.univ.t.G) →* (Over.mk x' ⟶ Xo.univ.t.G)} (hf : IsHkIsog p x x' C ψ f)
    (hg : IsHkIsog p x x' C ψ g) : f = g := by sorry
