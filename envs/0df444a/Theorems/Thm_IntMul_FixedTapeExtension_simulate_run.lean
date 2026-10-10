-- Prove2me | Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
-- name    : IntMul.FixedTapeExtension.simulate_run
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T23:56:44.954043+00:00
-- url     : https://prove2.me/theorems/90eed027-d7f7-41e7-b482-386ecbdd231a
-- title:
--   Literal old-machine execution preserving an added tape and its head at the exact original clock
-- statement:
--   For every finite k-tape machine, old configuration c, arbitrary saved configuration on the additional tape and clock T, the constructed k+1-tape machine reaches exactly the embedding of the old T-step configuration after exactly T physical transitions. Every old tape cell and head is the old machine result; every added-tape cell and its head equals its saved value. The alphabet and finite control are unchanged, and no additional seeking or dispatch is introduced. This allows existing physical bank services to run while a continuation stack remains intact on one fixed additional tape.
-- source:
--   Original exact-clock tape extension for saved continuation records in integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_FixedTapeExtension
import Mathlib.Tactic

open IntMul IntMul.FixedTapeExtension

theorem IntMul.FixedTapeExtension.simulate_run (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg) (T : ℕ) :
    (machine M).step^[T] (embed M base c) = embed M base (M.step^[T] c) ∧
    ((machine M).step^[T] (embed M base c)).cells (extraTape M) = base.cells (extraTape M) ∧
    ((machine M).step^[T] (embed M base c)).head (extraTape M) = base.head (extraTape M) ∧
    (∀ j, ((machine M).step^[T] (embed M base c)).cells (oldTape M j) = (M.step^[T] c).cells j) ∧
    (∀ j, ((machine M).step^[T] (embed M base c)).head (oldTape M j) = (M.step^[T] c).head j) := by sorry
