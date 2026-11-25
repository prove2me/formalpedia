-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_UnrExt_exists_ring
-- name    : GlobalTheory.UnitLemma.UnrExt.exists_ring
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:38:47.355453+00:00
-- url     : https://prove2.me/theorems/eafec64e-ccfd-4947-bcfe-03b5a5df85d7
-- title:
--   Unr Ext: exists ring
-- statement:
--   The Unr Ext construction uses the exists ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnramifiedOddDegreeQuadraticLocalExt.lean#L92-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnramifiedOddDegreeQuadraticLocalExt.lean#L92-L257

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedOddDegreeQuadraticLocalExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial IsLocalRing
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnrExt
open ReciprocityTheory.ChartRestriction.G.Semi

theorem GlobalTheory.UnitLemma.UnrExt.exists_ring (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] (p : ℕ) [Fact p.Prime] [CharP (ResidueField O) p]
    {q f d : ℕ} (hq : Nat.card (ResidueField O) = q ^ 2) (hf : q = p ^ f) (hd : Odd d) (c : O →+* O)
    (hcc : ∀ x, c (c x) = x) (hc : ∀ x, residue O (c x) = residue O x ^ q) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (_ : Finite (ResidueField W)) (_ : Algebra O W) (c' : W →+* W) (z : W),
      Module.Finite O W ∧ Function.Injective (algebraMap O W) ∧
      (∀ ϖ : O, Irreducible ϖ → Irreducible (algebraMap O W ϖ)) ∧ Module.finrank O W = d ∧
      Nat.card (ResidueField W) = (q ^ d) ^ 2 ∧ (∀ y, c' (c' y) = y) ∧
      (∀ x, c' (algebraMap O W x) = algebraMap O W (c x)) ∧ z - c' z ∉ maximalIdeal W ∧
      IsPrimitiveRoot z ((q ^ d) ^ 2 - 1) ∧ Algebra.adjoin O {z} = ⊤ := by sorry
