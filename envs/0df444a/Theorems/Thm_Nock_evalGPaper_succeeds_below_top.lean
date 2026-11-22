-- Prove2me | Theorems.Thm_Nock_evalGPaper_succeeds_below_top
-- name    : Nock.evalGPaper_succeeds_below_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:29:27.947805+00:00
-- url     : https://prove2.me/theorems/ae8733c3-b598-4339-b392-b5977f4e4df0
-- title:
--   Nock: eval GPaper succeeds below top
-- statement:
--   One residue below the top the guard holds and all three fragment oracles agree.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L353-L360
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L353-L360

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.evalGPaper_succeeds_below_top :
    evalGPaper 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) ∧
      evalPaperMod 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) ∧
      evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) := by sorry
