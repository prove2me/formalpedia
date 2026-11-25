-- Prove2me | Theorems.Thm_GlobalTheory_InvFieldBasis_evalPt_expPt
-- name    : GlobalTheory.InvFieldBasis.evalPt_expPt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:08:08.550566+00:00
-- url     : https://prove2.me/theorems/d97dd02e-4ab1-4bfe-9450-67f07da63fee
-- title:
--   Inv Field Basis: eval Pt exp Pt
-- statement:
--   The Inv Field Basis construction uses the eval Pt exp Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PreimageTranslate.lean#L177-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PreimageTranslate.lean#L177-L211

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningFieldStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PreimageTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS GlobalTheory.TangentOrigin GlobalTheory.SqZero GlobalTheory.LieBaseChange
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD pushR pullR fB)
open TrivSqZeroExt (inl inr)
noncomputable section
open GlobalTheory GlobalTheory.InvFieldBasis
variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] {n : ℕ}
variable {C : Type} [CommRing C] [Algebra K C]
variable {B : Type} [CommRing B] [Algebra K B]

theorem GlobalTheory.InvFieldBasis.evalPt_expPt {v : Fin n → (epsR K ⟶ G)} (hv : ∀ i, IsTangent (v i))
    {dd : Fin n → ∀ O : G.left.Opens, Γ(G.left, O) → Γ(G.left, O)} (hd : ∀ i, IsInvDer (v i) (dd i))
    (e : Fin n → B) (he : ∀ i j, e i * e j = 0)
    (z : sp (R₀ := K) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O) :
    ∃ h' : ⊤ ≤ (expPt v e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
      evalPt _ O h' f = evalPt z.left O h f + ∑ i, e i * evalPt z.left O h (dd i O f) := by sorry
