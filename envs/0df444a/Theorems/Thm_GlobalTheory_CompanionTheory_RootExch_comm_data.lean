-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_comm_data
-- name    : GlobalTheory.CompanionTheory.RootExch.comm_data
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:01:14.87852+00:00
-- url     : https://prove2.me/theorems/ba25083a-2ee7-4776-8edf-8b66856746d0
-- title:
--   Root Exch: comm data
-- statement:
--   The Root Exch construction uses the comm data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L221-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L221-L318

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RootExch
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.RootExch.comm_data {Φ Ψ : ι → ι → Prop} {E : ι → ι → K} (ψ₀ : AddChar K ℂ) (hΦ : IsPat Φ)
    (hsupp : ∀ i j, E i j ≠ 0 → Φ i j) (p q r t : ι)
    (hcomp : ∀ i j k, Φ i j → Φ j k → E i k ≠ 0 → i = p ∧ k = q)
    (g : GL ι K) (hg : g ∈ patSet K Φ) (hgi : g⁻¹ ∈ patSet K Φ) (hrt : Φ r t)
    (hΨ : ∀ i j, (i = r ∨ Φ i r) → (t = j ∨ Φ t j) → ¬ (i = r ∧ j = t) → Ψ i j)
    (hErt : E r t = 0) (h : r ≠ t) (s : K) :
    tv r t h s * g * (tv r t h s)⁻¹ * g⁻¹ ∈ patSet K Ψ ∧
      patChar E ψ₀ (tv r t h s * g * (tv r t h s)⁻¹ * g⁻¹) =
        ψ₀ (-(s * E p q * (g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q)) := by sorry
