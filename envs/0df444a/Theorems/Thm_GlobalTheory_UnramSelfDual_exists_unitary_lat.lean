-- Prove2me | Theorems.Thm_GlobalTheory_UnramSelfDual_exists_unitary_lat
-- name    : GlobalTheory.UnramSelfDual.exists_unitary_lat
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:47:01.417395+00:00
-- url     : https://prove2.me/theorems/770ace43-8da6-410e-94a5-3e10ff457dbe
-- title:
--   Unram Self Dual: exists unitary lat
-- statement:
--   The Unram Self Dual construction uses the exists unitary lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsOfFixedInt.lean#L324-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsOfFixedInt.lean#L324-L334

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

theorem GlobalTheory.UnramSelfDual.exists_unitary_lat {L' : Submodule O (Fin M → A)}
    (hL : ∀ y, y ∈ L ↔ ∀ z ∈ L, hform c J z y ∈ O)
    (hL' : ∀ y, y ∈ L' ↔ ∀ z ∈ L', hform c J z y ∈ O) {e e' : Fin M → Fin M → A}
    (heL : ∀ i, e i ∈ L) (he : ∀ i j, hform c J (e i) (e j) = if i = j then 1 else 0)
    (heL' : ∀ i, e' i ∈ L') (he' : ∀ i j, hform c J (e' i) (e' j) = if i = j then 1 else 0) :
    ∃ g ∈ UJ c J, (∀ i, (g : Matrix (Fin M) (Fin M) A) *ᵥ e i = e' i) ∧
      ∀ y, y ∈ L ↔ (g : Matrix (Fin M) (Fin M) A) *ᵥ y ∈ L' := by sorry
