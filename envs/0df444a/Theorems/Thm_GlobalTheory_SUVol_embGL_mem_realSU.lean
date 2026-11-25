-- Prove2me | Theorems.Thm_GlobalTheory_SUVol_embGL_mem_realSU
-- name    : GlobalTheory.SUVol.embGL_mem_realSU
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:27:57.806133+00:00
-- url     : https://prove2.me/theorems/92510c51-34b6-44fc-bd50-ddd3cfc9e94c
-- title:
--   SUVol: emb GL mem real SU
-- statement:
--   The SUVol construction uses the emb GL mem real SU property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EmbGLMemRealSU.lean#L221-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EmbGLMemRealSU.lean#L221-L238

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Statements_PlaceShiftStatements_DefiniteBound
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EmbGLMemRealSU_dd53fabb718cd1c0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SUVol
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped ENNReal NNReal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.SUVol.embGL_mem_realSU (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (γ : GL (Fin r) E) (h1 : (γ : Matrix (Fin r) (Fin r) E).det = 1)
    (h2 : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y) :
    _root_.GlobalTheory.SUVol.embGL Ψ r γ ∈ _root_.GlobalTheory.SUVol.realSU Ψ G := by sorry
