-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_cr23_progDec_stmt
-- name    : LinearSetReconciliation327.Main.cr23_progDec_stmt
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-21T12:01:39.879325+00:00
-- url     : https://prove2.me/theorems/bf3fc13d-cf8b-4ff0-b87a-0cc3607cf90c
-- title:
--   Proposition 2.3's decoder is a compiled statement
-- statement:
--   The decoder program $\mathrm{progDec}$ of Proposition 2.3 is compiled from a single source-level statement $S_{\mathrm{dec}}$ of the word-RAM programming language, i.e. there is a `Stmt` $S_{\mathrm{dec}}$ with $S_{\mathrm{dec}}.\mathrm{compile}(0) \mathbin{+\!+} [\mathrm{halt}] = \mathrm{progDec}$ $-$ so the decoder is a relocatable block and can be sequenced with a further stage, which is impossible for the bare `Program` that Proposition 2.3 exports, since its jump targets are absolute.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), §2.3 (Proposition 2.3: the CR23 decoder program); CR23 construction from M. Cheraghchi and I. Ribeiro, *Simple Codes for Sparse Recovery*, arXiv:1901.02852. Extracted from the verified development `Solutions/Sol_proposition_2_3.lean` §3 (`def decStmt`, `def progDec`).

import Definitions.Def_LinearSetReconciliation327_Main_CR23Dec

namespace LinearSetReconciliation327.Main

theorem cr23_progDec_stmt : ∃ (Sdec : Stmt), Sdec.compile 0 ++ [iHalt] = progDec := by sorry

end LinearSetReconciliation327.Main
