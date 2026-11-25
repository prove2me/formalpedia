-- Prove2me | Theorems.Thm_GlobalTheory_LatticeCovolumeL2_exists_line_basis
-- name    : GlobalTheory.LatticeCovolumeL2.exists_line_basis
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:00:24.592303+00:00
-- url     : https://prove2.me/theorems/8eb0a874-c024-4f27-85dd-e263482cc261
-- title:
--   Lattice Covolume L2: exists line basis
-- statement:
--   The Lattice Covolume L2 construction uses the exists line basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsLineBasis.lean#L205-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsLineBasis.lean#L205-L304

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsLineBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LatticeCovolumeL2
open NumberField Matrix
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.LatticeCovolumeL2.exists_line_basis {La ι V : Type} [AddCommGroup La] [Module (𝓞 E) La] [Fintype ι]
    [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (ψ : La →ₗ[𝓞 E] V) (hψ : Function.Injective ψ) (T : La → Prop) (b : ι → La)
    (hT : ∀ (c : 𝓞 E) v, T v → T (c • v)) (hsat : ∀ (m : ℤ) v, m ≠ 0 → T (m • v) → T v)
    (hb : ∀ v, T v → v ∈ Submodule.span ℤ (Set.range b)) (hι : Fintype.card ι ≤ Module.finrank ℚ E)
    (t : La) (ht : T t) (h0 : ψ t ≠ 0) :
    Fintype.card ι = Module.finrank ℚ E ∧ ∃ a : ι → E, (∀ k, ψ (b k) = a k • ψ t) ∧
      ∀ e : E, e • ψ t ∈ LinearMap.range ψ ↔ e ∈ Submodule.span ℤ (Set.range a) := by sorry
