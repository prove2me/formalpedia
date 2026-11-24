-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_exists_twist
-- name    : GlobalTheory.CompanionTheory.RootExch.exists_twist
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:01:09.285727+00:00
-- url     : https://prove2.me/theorems/ffdf31f5-5d44-47a8-9cc8-a43e870045e1
-- title:
--   Root Exch: exists twist
-- statement:
--   The Root Exch construction uses the exists twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L320-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L320-L344

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

theorem GlobalTheory.CompanionTheory.RootExch.exists_twist {Φ Ψ : ι → ι → Prop} {E : ι → ι → K} (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (hΦ : IsPat Φ)
    (hsupp : ∀ i j, E i j ≠ 0 → Φ i j) (p q r t : ι)
    (hcomp : ∀ i j k, Φ i j → Φ j k → E i k ≠ 0 → i = p ∧ k = q)
    (g : GL ι K) (hg : g ∈ patSet K Φ) (hgi : g⁻¹ ∈ patSet K Φ) (hrt : Φ r t) (hΨrt : Ψ r t)
    (hΨ : ∀ i j, (i = r ∨ Φ i r) → (t = j ∨ Φ t j) → ¬ (i = r ∧ j = t) → Ψ i j)
    (hErt : E r t = 0) (hEpq : E p q ≠ 0)
    (hne : (g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q ≠ 0) :
    ∃ h ∈ patSet K Ψ, h * g * h⁻¹ * g⁻¹ ∈ patSet K Ψ ∧ patChar E ψ₀ (h * g * h⁻¹ * g⁻¹) ≠ 1 := by sorry
