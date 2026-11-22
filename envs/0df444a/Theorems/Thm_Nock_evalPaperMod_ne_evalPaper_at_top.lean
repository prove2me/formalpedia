-- Prove2me | Theorems.Thm_Nock_evalPaperMod_ne_evalPaper_at_top
-- name    : Nock.evalPaperMod_ne_evalPaper_at_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:28:15.930366+00:00
-- url     : https://prove2.me/theorems/dba9bd0c-2905-4782-8115-77f470eee14c
-- title:
--   Nock: eval Paper Mod ne eval Paper at top
-- statement:
--   **Modular OP₄ differs from the unbounded increment at the top atom.**  On `+(2)` at `q = 3`
--       the modular oracle wraps (`(2+1) mod 3 = 0`) while the unbounded `evalPaper` produces `3`.
--       This is the compiled distinction: the strict paper language is the modular one, not the
--       unbounded `evalPaper`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperReferenceMod.lean#L159-L162
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperReferenceMod.lean#L159-L162

module
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Definitions.Def_LeanPool_PureNock_ModularEval
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.evalPaperMod_ne_evalPaper_at_top :
    evalPaperMod 3 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 2)))
      ≠ evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 2))) := by sorry
