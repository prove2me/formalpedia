-- Prove2me | Theorems.Thm_GlobalTheory_exists_adapted_lieBasis
-- name    : GlobalTheory.exists_adapted_lieBasis
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:51:13.102113+00:00
-- url     : https://prove2.me/theorems/21f9ae2a-f1de-44b0-9964-c3e8d271e423
-- title:
--   Global Theory: exists adapted lie Basis
-- statement:
--   The Global Theory construction uses the exists adapted lie Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAdaptedLieBasis.lean#L153-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAdaptedLieBasis.lean#L153-L208

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSumSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffOfFieldExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAdaptedLieBasis
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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open ReciprocityTheory.ChartRestriction.G.Chart (tvec)

theorem GlobalTheory.exists_adapted_lieBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (act : OAct (𝓞 E) G) (ρ : K), Smooth G.hom → DetCond D act (𝟙 (Sp K)) ρ → ∃ (g : ℕ) (v : Fin g → (epsR K ⟶ G)) (ty : Fin g → (𝓞 E →+* K)), IsLieBasis v ∧ (∀ τ : 𝓞 E →+* K, (τ H.rt = ρ → Nat.card {i // ty i = τ} = D.p) ∧ (τ H.rt ≠ ρ → Nat.card {i // ty i = τ} = D.q)) ∧ ∀ a j, IsLieComb (fun i => Matrix.diagonal (fun i => ty i a) i j) v (v j ≫ act.act a) := by sorry
