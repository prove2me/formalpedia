-- Prove2me | Theorems.Thm_GlobalTheory_pSerFrob_of_invariance
-- name    : GlobalTheory.pSerFrob_of_invariance
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:15:34.309615+00:00
-- url     : https://prove2.me/theorems/fe3a613a-5aa6-4564-8c60-7b8fb5a39aed
-- title:
--   Global Theory: p Ser Frob of invariance
-- statement:
--   The Global Theory construction uses the p Ser Frob of invariance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PSerFrobOfInvariance.lean#L39-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PSerFrobOfInvariance.lean#L39-L142

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_PSerFrobStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PSerFrobOfInvariance
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

theorem GlobalTheory.pSerFrob_of_invariance :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (n : ℕ) (S : Type) [CommRing S] [Algebra R₀ S], (n : S) = 0 → ∀ a e : Fin g → S, (∀ i, IsNilpotent (a i)) →
    (∀ i j, e i * e j = 0) → nsmulF ch.F (a + e) n = nsmulF ch.F a n) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] (g N : ℕ) (G : MvPolynomial (Fin g) R₀),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S], (p : S) = 0 → ∀ a e : Fin g → S, (∀ i, a i ^ N = 0) → (∀ i j, e i * e j = 0) →
      MvPolynomial.aeval (a + e) G = MvPolynomial.aeval a G) →
    ∀ m : Fin g →₀ ℕ, (∀ i, m i < N) → (∃ i, ¬ p ∣ m i) → ∃ r : R₀, MvPolynomial.coeff m G = p * r) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] {g : ℕ} {B : BX R₀} (K : LAlg R₀) (ch : FormalChartAtZero B K g), PSerFrobStatement p K ch) := by sorry
