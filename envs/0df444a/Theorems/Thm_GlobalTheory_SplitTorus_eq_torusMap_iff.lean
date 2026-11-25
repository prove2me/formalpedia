-- Prove2me | Theorems.Thm_GlobalTheory_SplitTorus_eq_torusMap_iff
-- name    : GlobalTheory.SplitTorus.eq_torusMap_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:24:24.754897+00:00
-- url     : https://prove2.me/theorems/e05ce11f-269f-5cc1-96a1-035b37373754
-- title:
--   Split Torus: eq torus Map iff
-- statement:
--   The Split Torus construction uses the eq torus Map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HomBaseChangeBijectiveOfLeNilradical.lean#L231-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HomBaseChangeBijectiveOfLeNilradical.lean#L231-L233

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open AddMonoidAlgebra (single)
open GlobalTheory
open GlobalTheory.SplitTorus
variable {S : Scheme.{u}} {X Y Z : Type u} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  {T T' : Over S}

theorem GlobalTheory.SplitTorus.eq_torusMap_iff (f : splitTorus S X ⟶ splitTorus S Y) (φ : Y →+ X) :
    f = torusMap S φ ↔ ∀ b, f.left.appTop.hom (chi Y b) = chi X (φ b) := by sorry
