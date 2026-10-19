-- Prove2me | Theorems.Thm_IntMul_Kappa_halted_multitape_step_fixed
-- name    : IntMul.Kappa.halted_multitape_step_fixed
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T21:57:08.462665+00:00
-- url     : https://prove2.me/theorems/dec26a9f-933d-4793-ab7f-e3701359064a
-- title:
--   Halted multitape configurations are fixed by one machine transition
-- statement:
--   For the exact Prove2Me multitape machine structure, if a configuration state is qHalt, executing one step leaves the entire configuration unchanged: state, every tape cell and every head. This is the frozen-halting invariant needed to pad fixed-time machine executions and compose tape routines. The proof uses the actual machine step definition and Function.update_eq_self, not an assumed simulator contract.
-- source:
--   Authoritative IntMul_MultitapeModel on Prove2Me, UUID 47ff1689-4e87-4af2-9406-674787e32429, based on A. Montanaro Computational Complexity notes, section 3.

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

theorem IntMul.Kappa.halted_multitape_step_fixed
    (M : IntMul.MultitapeTM) (c : M.Cfg)
    (hc : c.state = M.qHalt) : M.step c = c := by sorry
