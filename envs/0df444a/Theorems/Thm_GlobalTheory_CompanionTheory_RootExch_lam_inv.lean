-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_lam_inv
-- name    : GlobalTheory.CompanionTheory.RootExch.lam_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:03.305786+00:00
-- url     : https://prove2.me/theorems/8c87f7bd-dd7b-460d-9408-52ea7b45c68f
-- title:
--   Root Exch: lam inv
-- statement:
--   The Root Exch construction uses the lam inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L20-L25

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
variable {G : Type*} [Group G] [Fintype G]

theorem GlobalTheory.CompanionTheory.RootExch.lam_inv (H : Subgroup G) (lam : G → ℂ)
    (hm : ∀ a ∈ H, ∀ b ∈ H, lam (a * b) = lam a * lam b) (hne : ∀ a ∈ H, lam a ≠ 0)
    (a : G) (ha : a ∈ H) : lam a⁻¹ = (lam a)⁻¹ := by sorry
