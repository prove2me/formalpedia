-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Unram_mem_coset
-- name    : GlobalTheory.RootEx.Unram.mem_coset
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:29:35.58578+00:00
-- url     : https://prove2.me/theorems/cc0bd48a-69c3-4e51-a261-58d93de09018
-- title:
--   Unram: mem coset
-- statement:
--   The Unram construction uses the mem coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEmbXMul.lean#L85-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEmbXMul.lean#L85-L136

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Unram
open GlobalTheory.StepData
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [Fintype n']

theorem GlobalTheory.RootEx.Unram.mem_coset {p : ℕ} (h : GL (n ⊕ Fin c) k) (x₀ : Matrix n n' k)
    (e) (hA : IntM ((h⁻¹).val * affPt (c := c) p x₀ e))
    (hB : ∀ D : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k, (∀ r s, ¬ Free p (r, s) → D r s = 0) →
      IntM ((h⁻¹).val * D) → ch D ∈ 𝒪[k]) :
    ∃ r ∈ R k n c p, ∃ w ∈ KO k (n ⊕ Fin c), h = r * w := by sorry
