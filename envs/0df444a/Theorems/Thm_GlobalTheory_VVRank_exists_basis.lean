-- Prove2me | Theorems.Thm_GlobalTheory_VVRank_exists_basis
-- name    : GlobalTheory.VVRank.exists_basis
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:58:49.575714+00:00
-- url     : https://prove2.me/theorems/a8fcc651-4fb5-4882-b97f-a7ecb3f0dd16
-- title:
--   VVRank: exists basis
-- statement:
--   The VVRank construction uses the exists basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SpanEqTopOfFunctionals.lean#L257-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SpanEqTopOfFunctionals.lean#L257-L300

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
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
open GlobalTheory GlobalTheory.VVRank
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}

theorem GlobalTheory.VVRank.exists_basis (P : PolAV S) (n : ℕ) {V : S.Opens} {κ : Type} [Fintype κ]
    (b : κ → LB.Sec (LPow P.A P.L n (overRes (T := baseOver S) V)))
    (hb : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S) V).left)
        (b' : κ → LB.Sec (LPow P.A P.L n (baseAt t))),
        (∀ i, IsPullSec P.A P.L n (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i) (b' i)) →
        LinearIndependent Γ((baseAt t).left, ⊤)
            (fun i => (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))) ∧
          Submodule.span Γ((baseAt t).left, ⊤)
            (Set.range fun i => (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))) = ⊤)
    (T : Over S) [IsAffine T.left] (h : T ⟶ overRes (T := baseOver S) V) :
    ∃ c : Module.Basis κ Γ(T.left, ⊤) (SecM P.A P.L n T),
      ∀ i, c i = pullM P.A P.L n h (SecM.ofSec P.A (b i)) := by sorry
