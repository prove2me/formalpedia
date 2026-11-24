-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFixedAut_exists_eigenvector
-- name    : GlobalTheory.TorsionFixedAut.exists_eigenvector
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:08:52.4888+00:00
-- url     : https://prove2.me/theorems/e0d51138-4245-4880-bbc9-2c6f6ec63278
-- title:
--   Torsion Fixed Aut: exists eigenvector
-- statement:
--   The Torsion Fixed Aut construction uses the exists eigenvector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqIdOfFixesTorsion.lean#L189-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqIdOfFixesTorsion.lean#L189-L197

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.TorsionFixedAut
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

theorem GlobalTheory.TorsionFixedAut.exists_eigenvector {K R M : Type} [Field K] [IsAlgClosed K] [CommRing R] (e : K ≃+* R) [AddCommGroup M]
    [Module R M] (hM : Module.finrank R M ≠ 0) (f : M →ₗ[R] M) : ∃ (a : R) (v : M), v ≠ 0 ∧ f v = a • v := by sorry
