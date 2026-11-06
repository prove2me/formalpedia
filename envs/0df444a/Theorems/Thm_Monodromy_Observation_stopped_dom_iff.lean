-- Prove2me | Theorems.Thm_Monodromy_Observation_stopped_dom_iff
-- name    : Monodromy.Observation.stopped_dom_iff
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:37:37.460879+00:00
-- url     : https://prove2.me/theorems/73fbb8f7-6cb4-4a66-9abc-8f5b59b6d9c9
-- title:
--   Termination Is Equivalent to a Visit Under the Total Successor
-- statement:
--   For any type S, total successor A:S→S, Boolean stopping test b:S→Bool and initial state s∈S, evaluate the optional step that returns none when b is true and otherwise returns A(s). This partial evaluation is defined if and only if $b(A^n(s))=\mathrm{true}$ for some natural n, including n=0.
--
--   Statement dependencies: `Monodromy.Observation.stopped`.
--
--   Original proof dependencies: `Monodromy.Observation.stopped`.
--
--   Statement elaboration dependencies: `Monodromy.Observation.stopped`.
--
--   Proof elaboration dependencies: `Monodromy.Observation.stopped`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Observation.lean (file SHA-256 7989443c07eb69c1a560c79f678d827f7e8efd3f352ab0119eebb2cac76505bd):
--   Monodromy.Observation.stopped_dom_iff at L64-L91 [UTF-8 2520:4077].

module
public import Definitions.Def_Monodromy_Observation
public import Lean.Elab.Tactic.Omega
public import Mathlib.Computability.StateTransition
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

open Monodromy
open Monodromy.Observation
variable {S : Type*}

theorem Monodromy.Observation.stopped_dom_iff (next : S → S) (halt : S → Bool) (state : S) :
    (StateTransition.eval (stopped next halt) state).Dom ↔
      ∃ rounds : ℕ, halt ((next^[rounds]) state) = true := by sorry
