-- Prove2me | Theorems.Thm_GlobalTheory_SmoothLocusAdd_isSumAt_ptHom
-- name    : GlobalTheory.SmoothLocusAdd.isSumAt_ptHom
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:47:55.72886+00:00
-- url     : https://prove2.me/theorems/86946c14-044e-4d7f-ac1e-fc1866020454
-- title:
--   Smooth Locus Add: is Sum At pt Hom
-- statement:
--   The Smooth Locus Add construction uses the is Sum At pt Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsHomOfLocallyRel.lean#L83-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsHomOfLocallyRel.lean#L83-L104

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfLocallyRel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
  AlgebraicGeometry
noncomputable section
open GlobalTheory GlobalTheory.SmoothLocusAdd
open GlobalTheory.WeierstrassCurve
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
open WeierstrassCurve.Projective

theorem GlobalTheory.SmoothLocusAdd.isSumAt_ptHom {k : Type} [Field k] (ρ : R →+* k) {P Q S : Fin 3 → k}
    (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
    (hS : IsUnimodularSol (W.map ρ) S) (nP : (W.map ρ).toProjective.Nonsingular P)
    (nQ : (W.map ρ).toProjective.Nonsingular Q)
    (e : S ≈ (W.map ρ).toProjective.add P Q) :
    IsSumAt W (ptHom W ρ P hP) (ptHom W ρ Q hQ) (ptHom W ρ S hS) := by sorry
