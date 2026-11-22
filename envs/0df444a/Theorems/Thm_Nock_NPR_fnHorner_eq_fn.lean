-- Prove2me | Theorems.Thm_Nock_NPR_fnHorner_eq_fn
-- name    : Nock.NPR.fnHorner_eq_fn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:31:02.929932+00:00
-- url     : https://prove2.me/theorems/ba922d5d-e7cc-466c-99de-86f970ae63a5
-- title:
--   NPR: fn Horner eq fn
-- statement:
--   **`fnHorner` computes `NPR.fn`.**  The extractable Horner fingerprint equals the polynomial
--       fingerprint `fn` (`main.tex:1180–1184`), so `lem:ion_univariate_sec` /
--       `corr:ion_single_security`
--       (`Nock/NPR.lean`) transfer verbatim to the running code.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Fingerprint.lean#L57-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Fingerprint.lean#L57-L58

module
public import Definitions.Def_LeanPool_PureNock_NPR
public import Definitions.Def_LeanPool_PureNock_Fingerprint
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.NPR
open Polynomial
variable {K : Type*} [Field K]

theorem Nock.NPR.fnHorner_eq_fn (n : Noun) (r : K) : fnHorner r n = fn n r := by sorry
