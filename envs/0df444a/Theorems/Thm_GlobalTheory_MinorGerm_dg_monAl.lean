-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_dg_monAl
-- name    : GlobalTheory.MinorGerm.dg_monAl
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:47:54.932814+00:00
-- url     : https://prove2.me/theorems/dcae4aa0-ba1f-43de-8074-1201f011f452
-- title:
--   Minor Germ: dg mon Al
-- statement:
--   The Minor Germ construction uses the dg mon Al property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L273-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L273-L289

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] {σ : Type} {N N' : ℕ}

theorem GlobalTheory.MinorGerm.dg_monAl (j : Fin N × Fin N' → σ) (e : ℕ → ℕ) :
    dg j (monAl N N' e) =
      ∑ k ∈ Finset.Icc 1 (min N N'), e k • ∑ ρ ∈ Finset.range k, dgOne j ρ 1 := by sorry
