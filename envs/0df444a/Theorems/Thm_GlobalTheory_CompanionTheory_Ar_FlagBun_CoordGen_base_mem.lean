-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_base_mem
-- name    : GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.base_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:18:12.643237+00:00
-- url     : https://prove2.me/theorems/582ca4f9-5b04-4a28-9c74-45f20e4d859f
-- title:
--   Coord Gen: base mem
-- statement:
--   The Coord Gen construction uses the base mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L176-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L176-L185

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_FrameMatrixChartRatios
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
variable {Ω : Type} [Field Ω] {S : Type} {r : S → ℕ}
variable {E : Type} [AddCommGroup E] [Module Ω E] {n : S → ℕ}

theorem GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.base_mem (L : Subfield (GenField Ω r)) {κ : Type} (x : κ → Ω) (c₀ : κ)
    (hΩ : ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h)
    (hgen : ∀ j, algebraMap Ω (GenField Ω r) (x j / x c₀) ∈ L) (b : Ω) :
    algebraMap Ω (GenField Ω r) b ∈ L := by sorry
