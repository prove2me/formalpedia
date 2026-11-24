-- Prove2me | Theorems.Thm_GlobalTheory_UnramSelfDual_exists_image
-- name    : GlobalTheory.UnramSelfDual.exists_image
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:46:55.338799+00:00
-- url     : https://prove2.me/theorems/00fbb2cc-f7ac-4046-b931-ee1ad8e86368
-- title:
--   Unram Self Dual: exists image
-- statement:
--   The Unram Self Dual construction uses the exists image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsOfFixedInt.lean#L336-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsOfFixedInt.lean#L336-L356

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsSubConjNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsReflection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SelfDualLatticeProjectionMemOfUnitLength
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsOfFixedInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal Formalism.UG
open GlobalTheory GlobalTheory.UnramSelfDual
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {O : Subalgebra R A}
  {c : A →+* A} {M : ℕ} {J : Matrix (Fin M) (Fin M) A} {L : Submodule O (Fin M → A)}

theorem GlobalTheory.UnramSelfDual.exists_image (hfg : L.FG) (hsp : Submodule.span A (L : Set (Fin M → A)) = ⊤)
    (hL : ∀ y, y ∈ L ↔ ∀ z ∈ L, hform c J z y ∈ O) {g : GL (Fin M) A} (hg : g ∈ UJ c J) :
    ∃ L' : Submodule O (Fin M → A), L'.FG ∧ Submodule.span A (L' : Set (Fin M → A)) = ⊤ ∧
      (∀ y, y ∈ L' ↔ ∀ z ∈ L', hform c J z y ∈ O) ∧
      ∀ y ∈ L, (g : Matrix (Fin M) (Fin M) A) *ᵥ y ∈ L' := by sorry
