-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Unram_exists_embX_mul
-- name    : GlobalTheory.RootEx.Unram.exists_embX_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:30:06.939078+00:00
-- url     : https://prove2.me/theorems/5cea6b75-5ffd-4b43-a809-6641ba3d14c6
-- title:
--   Unram: exists emb X mul
-- statement:
--   The Unram construction uses the exists emb X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEmbXMul.lean#L14-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEmbXMul.lean#L14-L62

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

theorem GlobalTheory.RootEx.Unram.exists_embX_mul (m : GL (n ⊕ Fin c) k) (h1 : ∀ i r, m.val (Sum.inr i) r ∈ 𝒪[k])
    (h2 : ∀ i r, (m⁻¹).val r (Sum.inr i) ∈ 𝒪[k]) :
    ∃ g : GL n k, ∃ w ∈ KO k (n ⊕ Fin c), m = embX c g * w := by sorry
