-- Prove2me | Theorems.Thm_GlobalTheory_Diag_exists_prod_iff
-- name    : GlobalTheory.Diag.exists_prod_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T15:27:29.071097+00:00
-- url     : https://prove2.me/theorems/19a33503-9b10-410f-a7f2-aeb70cb4594c
-- title:
--   Diag: exists prod iff
-- statement:
--   The Diag construction uses the exists prod iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LeftEqIffLieVecSmul.lean#L226-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LeftEqIffLieVecSmul.lean#L226-L239

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LeftEqIffLieVecSmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent IsLieComb IsLieBasis OAct epsPt
  IsLieEigen LieMult)
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.Diag
variable {S : Scheme.{0}} {R : Type} [CommRing R] {g : Sp (DualNumber R) ⟶ S}
  {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

theorem GlobalTheory.Diag.exists_prod_iff (hg : ∀ a : R, g = spMap (epsScaleR a) ≫ g) {n : ℕ} (a : Fin n → R)
    (c : Fin n → (X →+ R)) (w : Over.mk g ⟶ splitTorus S X) :
    (∃ u : Fin n → (Over.mk g ⟶ splitTorus S X),
      (∀ i, (u i).left = spMap (epsScaleR (a i)) ≫ (epsVec g (c i)).left) ∧ w = (List.ofFn u).prod) ↔
      w = epsVec g (∑ i, a i • c i) := by sorry
