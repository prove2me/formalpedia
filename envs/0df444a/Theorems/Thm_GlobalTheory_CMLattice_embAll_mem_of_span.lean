-- Prove2me | Theorems.Thm_GlobalTheory_CMLattice_embAll_mem_of_span
-- name    : GlobalTheory.CMLattice.embAll_mem_of_span
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:03:31.418437+00:00
-- url     : https://prove2.me/theorems/ca72dbeb-dae2-4e30-8d7e-1ba736f41037
-- title:
--   CMLattice: emb All mem of span
-- statement:
--   The CMLattice construction uses the emb All mem of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/EqTopOfForallEmbAllMem.lean#L100-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/EqTopOfForallEmbAllMem.lean#L100-L120

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.CMLattice
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMLattice.embAll_mem_of_span (Ψ : Finset (E →+* ℂ)) (r : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E))
    (hΛ : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (S : Submodule ℝ (Ψ → Fin r → ℂ)) (hS : ∀ v ∈ Λ, embAll Ψ r v ∈ S) (v : Fin r → E) :
    embAll Ψ r v ∈ S := by sorry
