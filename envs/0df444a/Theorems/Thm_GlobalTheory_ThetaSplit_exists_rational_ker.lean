-- Prove2me | Theorems.Thm_GlobalTheory_ThetaSplit_exists_rational_ker
-- name    : GlobalTheory.ThetaSplit.exists_rational_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:04:35.733353+00:00
-- url     : https://prove2.me/theorems/fe6413ce-21b9-4d63-8ad3-e03e45a17fb0
-- title:
--   Theta Split: exists rational ker
-- statement:
--   The Theta Split construction uses the exists rational ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LbPowDescendsOfIsotropic.lean#L254-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LbPowDescendsOfIsotropic.lean#L254-L269

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LbPowDescendsOfIsotropic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.ThetaSplit

theorem GlobalTheory.ThetaSplit.exists_rational_ker {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] {A B : Over (Sp k)} [GrpObj B]
    (ψ : A ⟶ B) [IsFinite ψ.left] (t : Sp k' ⟶ Sp k) (x : Over.mk t ⟶ A) (hx : x ≫ ψ = 1) :
    ∃ c : 𝟙_ (Over (Sp k)) ⟶ A, c ≫ ψ = 1 ∧ x = toUnit _ ≫ c := by sorry
