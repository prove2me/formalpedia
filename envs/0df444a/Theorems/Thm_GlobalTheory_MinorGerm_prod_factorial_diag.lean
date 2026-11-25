-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_prod_factorial_diag
-- name    : GlobalTheory.MinorGerm.prod_factorial_diag
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:44:33.902812+00:00
-- url     : https://prove2.me/theorems/f3e94f06-f2a7-4f17-a814-97b856890813
-- title:
--   Minor Germ: prod factorial diag
-- statement:
--   The Minor Germ construction uses the prod factorial diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L397-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L397-L419

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
variable {p : σ → Prop} [DecidablePred p]

theorem GlobalTheory.MinorGerm.prod_factorial_diag (e : ℕ → ℕ) :
    ∏ x : Fin N × Fin N', (if x.1.val = x.2.val then monAl N N' e x.1.val else 0).factorial =
      ∏ ρ : Fin N, (monAl N N' e ρ.val).factorial := by sorry
