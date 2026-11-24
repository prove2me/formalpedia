-- Prove2me | Theorems.Thm_GlobalTheory_FlatDescent_hilbert90_local_of_cocycle
-- name    : GlobalTheory.FlatDescent.hilbert90_local_of_cocycle
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:32:25.045801+00:00
-- url     : https://prove2.me/theorems/cb9dc232-7308-444d-a284-7fc73de5b434
-- title:
--   Flat Descent: hilbert90 local of cocycle
-- statement:
--   The Flat Descent construction uses the hilbert90 local of cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/Hilbert90LocalOfCocycleTensor.lean#L8-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/Hilbert90LocalOfCocycleTensor.lean#L8-L133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvertibleOfFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_Hilbert90LocalOfCocycleTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.FlatDescent

theorem GlobalTheory.FlatDescent.hilbert90_local_of_cocycle : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R] [Module.Finite R S]
    [Module.FaithfullyFlat R S] (c : (S ⊗[R] S)ˣ),
    Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) (c : S ⊗[R] S) *
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)) (AlgHom.id R S) (c : S ⊗[R] S) =
      Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := S)) (AlgHom.id R S) (c : S ⊗[R] S) →
    ∀ p : Ideal R, p.IsPrime → ∃ r ∉ p, ∃ m s : S, ∃ n : ℕ,
      (m ⊗ₜ[R] (1 : S)) * (c : S ⊗[R] S) = (1 : S) ⊗ₜ[R] m ∧ m * s = algebraMap R S r ^ n := by sorry
