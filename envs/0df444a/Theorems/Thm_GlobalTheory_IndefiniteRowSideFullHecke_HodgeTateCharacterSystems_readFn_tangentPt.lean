-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HodgeTateCharacterSystems_readFn_tangentPt
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.readFn_tangentPt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:08:51.322853+00:00
-- url     : https://prove2.me/theorems/7037683e-e467-42ad-884d-64d75cc4a251
-- title:
--   Hodge Tate Character Systems: read Fn tangent Pt
-- statement:
--   The Hodge Tate Character Systems construction uses the read Fn tangent Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/HodgeTateCharacterSystems.lean#L163-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/HodgeTateCharacterSystems.lean#L163-L174

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HodgeTateCharacterSystems
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems
noncomputable section
variable {O : Type u} [CommRing O] [IsLocalRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G]

theorem GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.readFn_tangentPt {R : Type u} [CommRing R] [Algebra O R] (v : Cotangent G →ₗ[O] R)
    (s : Γ(G.left, ⊤)) :
    readFn ((tangentPt v).left.appTop.hom s) =
      tangentAlg v (G.left.presheaf.germ ⊤ (origin G) trivial s) := by sorry
