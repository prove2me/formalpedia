-- Prove2me | Theorems.Thm_GlobalTheory_moduli_point_from_fg_subalgebra
-- name    : GlobalTheory.moduli_point_from_fg_subalgebra
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:45.58481+00:00
-- url     : https://prove2.me/theorems/aed78efe-e1fe-5536-aacb-1a6537625530
-- title:
--   Global Theory: moduli point from fg subalgebra
-- statement:
--   The Global Theory construction uses the moduli point from fg subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ModuliPointFromFgSubalgebra.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ModuliPointFromFgSubalgebra.lean#L55-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ModuliPointFromFgSubalgebra
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
open GlobalTheory

theorem GlobalTheory.moduli_point_from_fg_subalgebra : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X), x ≫ Xo.s = sOf c S → ∃ S₀ : Subalgebra c.F S, S₀.FG ∧ ∃ x₀ : Sp S₀ ⟶ Xo.X, x₀ ≫ Xo.s = sOf c S₀ ∧ spMap S₀.val.toRingHom ≫ x₀ = x := by sorry
