-- Prove2me | Theorems.Thm_GlobalTheory_nsmulF_add_sqZero_eq
-- name    : GlobalTheory.nsmulF_add_sqZero_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:20:17.867122+00:00
-- url     : https://prove2.me/theorems/e53b9e6b-afaa-40e2-bb42-4efb9c7c415d
-- title:
--   Global Theory: nsmul F add sq Zero eq
-- statement:
--   The Global Theory construction uses the nsmul F add sq Zero eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NsmulFAddSqZeroEq.lean#L56-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NsmulFAddSqZeroEq.lean#L56-L118

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_PSerFrobStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NsmulFAddSqZeroEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory

theorem GlobalTheory.nsmulF_add_sqZero_eq :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
    ∃ M : Matrix (Fin g) (Fin g) S, (∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) S) k j ∈ Ideal.span (Set.range a)) ∧
      ∀ e : Fin g → S, (∀ i j, e i * e j = 0) → fAdd ch.F a e = a + M *ᵥ e) →
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (n : ℕ) (S : Type) [CommRing S] [Algebra R₀ S], (n : S) = 0 → ∀ a e : Fin g → S, (∀ i, IsNilpotent (a i)) →
    (∀ i j, e i * e j = 0) → nsmulF ch.F (a + e) n = nsmulF ch.F a n) := by sorry
