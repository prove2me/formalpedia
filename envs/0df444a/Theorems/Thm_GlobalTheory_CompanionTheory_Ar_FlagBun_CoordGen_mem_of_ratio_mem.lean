-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_mem_of_ratio_mem
-- name    : GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.mem_of_ratio_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:17:27.07533+00:00
-- url     : https://prove2.me/theorems/6fba076f-fe08-4ca4-87cf-bb2a970d33ce
-- title:
--   Coord Gen: mem of ratio mem
-- statement:
--   The Coord Gen construction uses the mem of ratio mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L187-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L187-L220

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

theorem GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.mem_of_ratio_mem [Fintype S] (κ : Type) (x : κ → Ω) (φ : ∀ s, Fin (n s) → Module.Dual Ω E)
    (c : ∀ s, Fin (r s) → E) (c₀ : κ) (hx0 : x c₀ ≠ 0)
    (hΩ : ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h)
    (B : ∀ s, Matrix (Fin (r s)) (Fin (n s)) Ω)
    (hB : ∀ s, B s * Matrix.of (fun j l => φ s j (c s l)) = 1)
    (ρ : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1))
    (hρ : ∀ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (ρ q) (Fin.castLE q.2.2)).det ≠ 0)
    (L : Subfield (GenField Ω r))
    (hratio : ∀ j : FlagIx κ n r, flagCoord κ x φ c j / flagCoord κ x φ c (c₀, ρ) ∈ L)
    (a : GenField Ω r) : a ∈ L := by sorry
