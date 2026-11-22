-- Prove2me | Theorems.Thm_Nock_evalGPaper_fails_where_evalPaperMod_wraps
-- name    : Nock.evalGPaper_fails_where_evalPaperMod_wraps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:29:26.940409+00:00
-- url     : https://prove2.me/theorems/8c3bdea9-ff3c-4195-ad5e-06f46f0f424b
-- title:
--   Nock: eval GPaper fails where eval Paper Mod wraps
-- statement:
--   **The guard rejects exactly the divergent computation.**  At the top residue `q−1 = 4` the
--       strict modular oracle wraps to `0` while the unbounded oracle produces `5`
--       (`evalPaperMod_ne_evalPaper_at_top`); the guarded fragment evaluator crashes there, so the
--       bridge never claims agreement across the wrap.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L344-L350
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L344-L350

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.evalGPaper_fails_where_evalPaperMod_wraps :
    evalGPaper 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 4))) = none ∧
      evalPaperMod 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 4)))
        = some (.atom 0) ∧
      evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 4)))
        = some (.atom 5) := by sorry
