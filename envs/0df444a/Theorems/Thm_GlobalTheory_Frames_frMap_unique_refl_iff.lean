-- Prove2me | Theorems.Thm_GlobalTheory_Frames_frMap_unique_refl_iff
-- name    : GlobalTheory.Frames.frMap_unique_refl_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:43.757577+00:00
-- url     : https://prove2.me/theorems/e852f51b-6802-4d7e-93ee-febb91fe2baf
-- title:
--   Frames: fr Map unique refl iff
-- statement:
--   The Frames construction uses the fr Map unique refl iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FramedPointBaseChangeUniqueReflIff.lean#L51-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FramedPointBaseChangeUniqueReflIff.lean#L51-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FramedPointBaseChangeUniqueReflIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory GlobalTheory.Frames

theorem GlobalTheory.Frames.frMap_unique_refl_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S), (∀ z z' : FrPt Xo c T, FrMap φ y z → FrMap φ y z' → z = z') ∧ FrMap (AlgHom.id c.F S) y y ∧ ∀ z : FrPt Xo c T, FrMap φ y z ↔ (z.x = spMap φ.toRingHom ≫ y.x ∧ (∀ τ i, z.u τ i = spMap (dualMap φ.toRingHom) ≫ y.u τ i) ∧ SecBC φ.toRingHom 1 y.x z.x y.s z.s) := by sorry
