-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_exists_smul_of_twCoord
-- name    : GlobalTheory.AbLaw.exists_smul_of_twCoord
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T15:09:05.28071+00:00
-- url     : https://prove2.me/theorems/9ea69927-8aef-56d6-bf45-01263351ab9f
-- title:
--   Ab Law: exists smul of tw Coord
-- statement:
--   The Ab Law construction uses the exists smul of tw Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulOfTwCoord.lean#L34-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulOfTwCoord.lean#L34-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulOfTwCoord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory

theorem GlobalTheory.AbLaw.exists_smul_of_twCoord :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y) (hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V) fun i t => SecOnR.mulSec f M t (s i) V) (V : Y.Opens) (F : MvPolynomial (Fin (m + 1)) R) (d t t' : ℤ) (y : SecOn (tw M H t) V), F ∈ polyGrading (Fin (m + 1)) R d → t' = t + d → ∃ y' : SecOn (tw M H t') V, F • GrSum.of (hx V) t (SecOnR.of f _ V y) = GrSum.of (hx V) t' (SecOnR.of f _ V y') ∧ ∀ (p : M.ι) (l : H.ι), SecOn.twCoord y' p l = rs Y (inf_le_right.trans inf_le_right : V ⊓ (M.U p ⊓ H.U l) ≤ H.U l) (MvPolynomial.eval₂Hom (cst f (H.U l)) (fun j => (s j).f l) F) * SecOn.twCoord y p l := by sorry
