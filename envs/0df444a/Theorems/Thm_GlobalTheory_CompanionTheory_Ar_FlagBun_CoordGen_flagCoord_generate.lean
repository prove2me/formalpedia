-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_flagCoord_generate
-- name    : GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.flagCoord_generate
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:59:20.427542+00:00
-- url     : https://prove2.me/theorems/4d65b140-6721-4ead-b996-ffc51ede11f8
-- title:
--   Coord Gen: flag Coord generate
-- statement:
--   The Coord Gen construction uses the flag Coord generate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L222-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L222-L244

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

theorem GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.flagCoord_generate (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type) [Fintype S]
    (r n : S → ℕ) (κ : Type) (x : κ → Ω) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (c₀ : κ)
    (hx0 : x c₀ ≠ 0)
    (hΩ : ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h)
    (hB : ∀ s, ∃ B : Matrix (Fin (r s)) (Fin (n s)) Ω, B * Matrix.of (fun j l => φ s j (c s l)) = 1) :
    ∃ J₀ : FlagIx κ n r, flagCoord κ x φ c J₀ ≠ 0 ∧ ∀ a : GenField Ω r,
      ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => flagCoord κ x φ c j / flagCoord κ x φ c J₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => flagCoord κ x φ c j / flagCoord κ x φ c J₀),
        h ≠ 0 ∧ a = g / h := by sorry
