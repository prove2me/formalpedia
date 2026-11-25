-- Prove2me | Theorems.Thm_GlobalTheory_LatticeLocBasis_exists_basis_up_to_fintype
-- name    : GlobalTheory.LatticeLocBasis.exists_basis_up_to_fintype
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:22:51.580464+00:00
-- url     : https://prove2.me/theorems/e9bc3135-3add-41b5-a13f-aea108e9bccc
-- title:
--   Lattice Loc Basis: exists basis up to fintype
-- statement:
--   The Lattice Loc Basis construction uses the exists basis up to fintype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsMatrixBasisLatticeUpToDenominatorNotMem.lean#L11-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsMatrixBasisLatticeUpToDenominatorNotMem.lean#L11-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMatrixBasisLatticeUpToDenominatorNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix Module
open scoped BigOperators nonZeroDivisors
open GlobalTheory GlobalTheory.LatticeLocBasis

theorem GlobalTheory.LatticeLocBasis.exists_basis_up_to_fintype {O A E : Type} [CommRing O] [CommRing A] [IsDomain A] [Field E] [Algebra O A]
    [Algebra A E] [Algebra O E] [IsScalarTower O A E] (S : Submonoid O) [IsLocalization S A] [IsFractionRing A E]
    [IsPrincipalIdealRing A] {n : Type} [Fintype n] (L : Submodule O (n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (n → E)) = ⊤) :
    ∃ (s : S) (b : n → n → E), LinearIndependent E b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, (s : O) • w ∈ Submodule.span O (Set.range b) := by sorry
