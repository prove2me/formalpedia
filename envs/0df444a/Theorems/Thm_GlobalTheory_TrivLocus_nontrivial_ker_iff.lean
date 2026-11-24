-- Prove2me | Theorems.Thm_GlobalTheory_TrivLocus_nontrivial_ker_iff
-- name    : GlobalTheory.TrivLocus.nontrivial_ker_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:13:27.840087+00:00
-- url     : https://prove2.me/theorems/03a51d91-3751-43ed-bb31-354279db64ef
-- title:
--   Triv Locus: nontrivial ker iff
-- statement:
--   The Triv Locus construction uses the nontrivial ker iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsKerIffMinors.lean#L42-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsKerIffMinors.lean#L42-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKerIffMinors
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
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.TrivLocus

theorem GlobalTheory.TrivLocus.nontrivial_ker_iff {R K : Type} [CommRing R] [Field K] (g : R →+* K) {a b : ℕ}
    (D : Matrix (Fin b) (Fin a) R) :
    Nontrivial {v : Fin a → K // (D.map g).mulVec v = 0} ↔
      ∀ σ : Fin a → Fin b, (D.submatrix σ id).det ∈ RingHom.ker g := by sorry
