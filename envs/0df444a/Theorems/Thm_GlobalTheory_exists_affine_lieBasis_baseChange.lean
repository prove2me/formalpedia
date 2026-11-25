-- Prove2me | Theorems.Thm_GlobalTheory_exists_affine_lieBasis_baseChange
-- name    : GlobalTheory.exists_affine_lieBasis_baseChange
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:50:06.221234+00:00
-- url     : https://prove2.me/theorems/5ddc5894-f90d-4252-b283-56d2224fcc23
-- title:
--   Global Theory: exists affine lie Basis base Change
-- statement:
--   The Global Theory construction uses the exists affine lie Basis base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsAffineLieBasisBaseChange.lean#L257-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsAffineLieBasisBaseChange.lean#L257-L288

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsAffineLieBasisBaseChange
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
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor MonObj
open scoped CategoryTheory.Obj

theorem GlobalTheory.exists_affine_lieBasis_baseChange (X : Scheme.{0}) (G : Over X) [GrpObj G] [Smooth G.hom] (x : X)
    (W : X.Opens) (hx : x ∈ W) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U), x ∈ U ∧ U ≤ W ∧
      ∃ (n : ℕ) (v₀ : Fin n → (Sp (DualNumber Γ(X, U)) ⟶ G.left)),
        ∀ (R' : Type) [CommRing R'] (f : Γ(X, U) →+* R') (G' : Over (Sp R')) [GrpObj G'] (φ : G'.left ⟶ G.left),
          IsGrpPullback G' G (spMap f ≫ hU.fromSpec) φ →
            ∃ v' : Fin n → (epsR R' ⟶ G'),
              (∀ j, (v' j).left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ v₀ j) ∧ IsLieBasis v' := by sorry
