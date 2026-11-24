-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_RatCoord_ofF_gram_iff
-- name    : GlobalTheory.CompanionTheory.SW.BB.RatCoord.ofF_gram_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:00:47.186884+00:00
-- url     : https://prove2.me/theorems/d348a52d-0b79-4df2-a259-a233e0a796ea
-- title:
--   Rat Coord: of F gram iff
-- statement:
--   The Rat Coord construction uses the of F gram iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateBijectionTraceForm.lean#L102-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateBijectionTraceForm.lean#L102-L148

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateBijectionTraceForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.RatCoord
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem GlobalTheory.CompanionTheory.SW.BB.RatCoord.ofF_gram_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
    IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
    Function.Bijective (ofF b : (Fin M × Fin d → F) → Fin 1 → Fin M → E) ∧
    (∀ x : Fin M × Fin d → F, ofF b x ≠ 0 ↔ x ≠ 0) ∧
    ∀ (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F),
      (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) =
        (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ
          (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) →
      ∀ (β : F) (x : Fin M × Fin d → F),
        gramE σ J (ofF b x) = (fun _ _ => algebraMap F E β) ↔
          (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β := by sorry
