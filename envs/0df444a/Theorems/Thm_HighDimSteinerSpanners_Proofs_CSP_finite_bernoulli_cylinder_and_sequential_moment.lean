-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_finite_bernoulli_cylinder_and_sequential_moment
-- name    : HighDimSteinerSpanners.Proofs.CSP.finite_bernoulli_cylinder_and_sequential_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:49:23.30832+00:00
-- url     : https://prove2.me/theorems/c44a5ad3-91e7-46f1-ab2a-2570fe911e3a
-- title:
--   CSP: finite bernoulli cylinder and sequential moment
-- statement:
--   The CSP construction uses the finite bernoulli cylinder and sequential moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Bernoulli.lean#L139-L359
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Bernoulli.lean#L139-L359

module
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessProjection
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Bernoulli
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section

theorem HighDimSteinerSpanners.Proofs.CSP.finite_bernoulli_cylinder_and_sequential_moment {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i : ι, 0 ≤ p i ∧ p i ≤ 1) :
    (∀ ω : ι → Bool, 0 ≤ bernWeight p ω) ∧
    (∑ ω : ι → Bool, bernWeight p ω = 1) ∧
    (∀ S : Finset ι,
      ∑ ω : ι → Bool, (if ∀ i ∈ S, ω i = true then bernWeight p ω else 0) = ∏ i ∈ S, p i) ∧
    (∀ (β γ : Type) [DecidableEq β] [DecidableEq γ]
      (Pool : Finset β) (K : ℕ) (α_step : ℝ),
      0 ≤ α_step →
      ∀ (Base : (ι → Bool) → Prop) [DecidablePred Base]
        (A : (ι → Bool) → Finset β),
        (∀ ω : ι → Bool, A ω ⊆ Pool) →
        ∀ (S₀ : Finset ι)
          (U : (m : ℕ) → (Fin m → β) → Finset ι)
          (M_wit : (m : ℕ) → (Fin m → β) → β → Finset γ)
          (Q : (m : ℕ) → (Fin m → β) → β → γ → Finset ι),
          (∀ z₀ : Fin 0 → β, S₀ ⊆ U 0 z₀) →
          (∀ m < K, ∀ (z_prev : Fin m → β) (b : β),
            U m z_prev ⊆ U (m + 1) (Fin.snoc z_prev b)) →
          (∀ m < K, ∀ z_prev : Fin m → β,
            Function.Injective z_prev → (∀ t : Fin m, z_prev t ∈ Pool) →
            ∀ b ∈ Pool \ Finset.univ.image z_prev, ∀ w ∈ M_wit m z_prev b,
              Q m z_prev b w ⊆ U (m + 1) (Fin.snoc z_prev b) \ U m z_prev) →
          (∀ ω : ι → Bool, Base ω →
            (∀ i ∈ S₀, ω i = true) ∧
            (∀ z : Fin K → β, Function.Injective z → (∀ m : Fin K, z m ∈ A ω) →
              ∀ m : Fin K,
                ∃ w ∈ M_wit m.1 (fun t : Fin m.1 => z (t.castLE (Nat.le_of_lt m.isLt))) (z m),
                  ∀ i ∈ Q m.1 (fun t : Fin m.1 => z (t.castLE (Nat.le_of_lt m.isLt))) (z m) w,
                    ω i = true)) →
          (∀ m < K, ∀ z_prev : Fin m → β,
            Function.Injective z_prev → (∀ t : Fin m, z_prev t ∈ Pool) →
            ∑ b ∈ Pool \ Finset.univ.image z_prev,
              ∑ w ∈ M_wit m z_prev b, (∏ i ∈ Q m z_prev b w, p i) ≤ α_step) →
          ∑ ω : ι → Bool, (if Base ω ∧ K ≤ (A ω).card then bernWeight p ω else 0) ≤
            (∏ i ∈ S₀, p i) * α_step ^ K) := by sorry
