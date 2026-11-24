-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_genU_mem
-- name    : GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.genU_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:18:03.266906+00:00
-- url     : https://prove2.me/theorems/71f8222e-288d-4994-b6db-f497a5693f8b
-- title:
--   Coord Gen: gen U mem
-- statement:
--   The Coord Gen construction uses the gen U mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L134-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L134-L155

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

theorem GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.genU_mem (L : Subfield (GenField Ω r)) (hbase : ∀ b : Ω, algebraMap Ω (GenField Ω r) b ∈ L)
    (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (s : S)
    (B : Matrix (Fin (r s)) (Fin (n s)) Ω)
    (hB : B * Matrix.of (fun j l => φ s j (c s l)) = 1) (k l : Fin (r s)) (hkl : k ≤ l)
    (ρ : Fin ((k : ℕ) + 1) → Fin (n s)) (hρ : ((flagMat φ c s).submatrix ρ (Fin.castLE k.2)).det ≠ 0)
    (hminor : ∀ f : Fin ((k : ℕ) + 1) → Fin (n s), ((flagMat φ c s).submatrix f (Fin.castLE k.2)).det /
        ((flagMat φ c s).submatrix ρ (Fin.castLE k.2)).det ∈ L) :
    genU Ω r s l k ∈ L := by sorry
