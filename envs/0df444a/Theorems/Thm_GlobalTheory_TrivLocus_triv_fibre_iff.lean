-- Prove2me | Theorems.Thm_GlobalTheory_TrivLocus_triv_fibre_iff
-- name    : GlobalTheory.TrivLocus.triv_fibre_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:24:27.731561+00:00
-- url     : https://prove2.me/theorems/009f116d-ebf3-42af-8da8-6d1fe64bfae7
-- title:
--   Triv Locus: triv fibre iff
-- statement:
--   The Triv Locus construction uses the triv fibre iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsKerIffMinors.lean#L149-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsKerIffMinors.lean#L149-L160

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
variable {X Y : Scheme.{0}}

theorem GlobalTheory.TrivLocus.triv_fibre_iff {R : Type} [CommRing R] {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (hM : M.IsLB)
    (P : Perf f M) (Q : Perf f (pw M (-1))) [IsProper f] [GeometricallyIntegral f]
    {K : Type} [Field K] (g : R →+* K) {X' : Scheme.{0}} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of K)}
    (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) :
    Triv (M.pull π) ↔ (∀ σ : Fin P.a → Fin P.b, (P.D₀.submatrix σ id).det ∈ RingHom.ker g) ∧
      ∀ σ : Fin Q.a → Fin Q.b, (Q.D₀.submatrix σ id).det ∈ RingHom.ker g := by sorry
