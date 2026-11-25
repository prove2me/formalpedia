-- Prove2me | Theorems.Thm_GlobalTheory_T_fdeg_eq_finrank_residueField_alt
-- name    : GlobalTheory.T.fdeg_eq_finrank_residueField_alt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:27:59.874042+00:00
-- url     : https://prove2.me/theorems/8fd463f0-694c-5cb7-9237-ba296f6f05ce
-- title:
--   T: fdeg eq finrank residue Field alt
-- statement:
--   The T construction uses the fdeg eq finrank residue Field alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FdegEqFinrankResidueFieldStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FdegEqFinrankResidueFieldStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FdegEqFinrankResidueField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FdegEqFinrankResidueFieldStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.fdeg_eq_finrank_residueField_alt : ∀ (R R' F : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F], Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (L : Type) [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L] (A : Type) [CommRing A] [Algebra R' A] (ϖ : R'), IsUnif A ϖ → ∀ (ζ : Pts R' A) [IsDVRAt ζ] (w : AddValuation L (WithTop ℤ)), w ∈ ValPl.PlacesOver R L → ∀ (S : Type) [CommRing S] (u : AddValuation S (WithTop ℤ)) (Ψ : A →+* S) (ι : L →+* S), Function.Surjective Ψ → (∀ r : R, Ψ (algebraMap R' A (algebraMap R R' r)) = ι (algebraMap R L r)) → (∀ g, u (ι g) = w g) → (∀ a, ord ϖ ζ a = u (Ψ a)) → (∀ x, 0 ≤ u x → ∃ g, 0 ≤ w g ∧ 0 < u (x - ι g)) → fdeg ζ = (letI := resAlg (F := F) w; Module.finrank (IsLocalRing.ResidueField ((vRing w).comap (algebraMap F L))) (IsLocalRing.ResidueField (vRing w))) := by sorry
