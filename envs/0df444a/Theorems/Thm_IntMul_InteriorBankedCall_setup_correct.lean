-- Prove2me | Theorems.Thm_IntMul_InteriorBankedCall_setup_correct
-- name    : IntMul.InteriorBankedCall.setup_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T21:28:33.944663+00:00
-- url     : https://prove2.me/theorems/624c217f-366b-4e02-9abc-8fb6c1ccc526
-- title:
--   Charged interior bank initialization with physical buffer erasure and saved caller data
-- statement:
--   For any finite child machine M, arbitrary saved caller configuration, buffer boundary sigma, child bank offsets and binary inputs x,y, the literal interior caller reaches the exact embedded initial child configuration after 2L+3 transitions, where L=|x|+|y|+1. It physically writes all local markers, copies the L input letters from the mutable buffer to the child input while erasing each source cell, detects the end blank, rewinds the child input head and dispatches. Every saved prefix is retained, the buffer suffix is entirely blank, all other child banks are blank after their new markers, and every child head is on its boundary. Empty and unequal-width inputs are included. This is a trace from the specified prepared frame: producing the input buffer and allocating fresh suffix banks are separate tasks.
-- source:
--   Original finite-tape compiler foundation for the integer-multiplication campaign. Written by Codex.

import Definitions.Def_IntMul_InteriorBankedCall
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

open IntMul IntMul.InteriorBankedCall

theorem IntMul.InteriorBankedCall.setup_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    (machine M).step^[2 * (BankedCall.inputWord M x y).length + 3]
      (inputFrame M base sigma offset x y) = readyFrame M base sigma offset x y := by sorry
