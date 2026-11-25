-- Prove2me | Theorems.Thm_GlobalTheory_Frames_frChg_exists_unique
-- name    : GlobalTheory.Frames.frChg_exists_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:25.658053+00:00
-- url     : https://prove2.me/theorems/16b8c51b-a3aa-4c2f-a74c-824c33acec8e
-- title:
--   Frames: fr Chg exists unique
-- statement:
--   The Frames construction uses the fr Chg exists unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FrameChangeExistsUniqueOfSamePoint.lean#L70-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FrameChangeExistsUniqueOfSamePoint.lean#L70-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameChangeExistsUniqueOfSamePoint
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
open GlobalTheory.Frames.ChgOf

theorem GlobalTheory.Frames.frChg_exists_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S), (y'.x = y.x → ∃ (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : Sˣ), (∀ τ, IsUnit (g τ).det) ∧ FrChg g (a : S) y y') ∧ ∀ (g g' : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a a' : S), FrChg g a y y' → FrChg g' a' y y' → g = g' ∧ a = a' := by sorry
