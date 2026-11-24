-- Prove2me | Theorems.Thm_GlobalTheory_CombMinor_prod_det_mem_HaO
-- name    : GlobalTheory.CombMinor.prod_det_mem_HaO
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:15:13.536259+00:00
-- url     : https://prove2.me/theorems/49ecc7c7-8e89-4d92-9a8d-98242d2e71e0
-- title:
--   Comb Minor: prod det mem Ha O
-- statement:
--   The Comb Minor construction uses the prod det mem Ha O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ProdDetMemHaO.lean#L119-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ProdDetMemHaO.lean#L119-L167

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ProdDetMemHaO
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
open scoped BigOperators
open Classical MvPolynomial Formalism.L2.Pj Formalism.L2.Pj.Crude
open GlobalTheory GlobalTheory.CombMinor
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k]

theorem GlobalTheory.CombMinor.prod_det_mem_HaO : ∀ (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (n : ℕ) (k : Type) [Field k] (O : Subring k) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ) (A : Type) [Fintype A] (σ : A → Ty) (s : A → ℕ) (hs : ∀ α, s α ≤ r (σ α)) (B : ∀ α, Fin (s α) → Fin n → k) (e : A → ℕ), (∀ α ρ b, B α ρ b ∈ O) → (∀ τ, cc τ ≠ τ) → (∀ α α', e α ≠ 0 → e α' ≠ 0 → σ α' = cc (σ α) → ∀ ρ ρ' b, B α ρ b = 0 ∨ B α' ρ' b = 0) → (∀ (τ : Ty) (i : Fin (r τ)), ∑ α ∈ Finset.univ.filter (fun α => σ α = τ ∧ i.val < s α), e α = a τ i) → (∏ α, (Matrix.of fun ρ i : Fin (s α) => ∑ b, MvPolynomial.C (B α ρ b) * (MvPolynomial.X ⟨σ α, Fin.castLE (hs α) i, b⟩ : MvPolynomial (Letter Ty r n) k)).det ^ e α) ∈ HaO r n k O cc isX a := by sorry
