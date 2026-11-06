-- Prove2me | Theorems.Thm_Monodromy_ReversibleCompilation_marked_firstReturn
-- name    : Monodromy.ReversibleCompilation.marked_firstReturn
-- status  : Open
-- author  : @nonlocally
-- created : 2026-11-05T22:13:48.819314+00:00
-- url     : https://prove2.me/theorems/99ae47bf-1c90-4b7e-9c8e-0ce748147d40
-- title:
--   A Marked Counter Return Lifts to a Native Marked Return
-- statement:
--   For a deterministic, target-compatible reversible two-counter table and a Boolean mark on source control positions, suppose one counter step takes `first` to `middle`, followed by a finite chain of counter steps to `last` whose sources are unmarked. If the initial and final source positions are marked, then the embedded configurations have the native first-return property: both native endpoints satisfy the marked boundary condition, one native step leaves the initial point, and the remaining native internal trajectory reaches the final point without passing an earlier marked source.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. src/Monodromy/Counter.lean, Monodromy.ReversibleCompilation.marked_firstReturn at L8581-L8591.

module
public import Definitions.Def_Monodromy_FormalCompilation

@[expose] public section

open Monodromy
open Monodromy.ReversibleCompilation
open Counter.Reversible CoupledContinuation
variable {q e : ℕ} [NeZero q]

theorem Monodromy.ReversibleCompilation.marked_firstReturn (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) {first middle last : State 2 q}
    (initial : Counter.Reversible.step table first = some middle)
    (rest : Relation.ReflTransGen (fun first last : State 2 q =>
      Counter.Reversible.step table first = some last ∧ mark first.1 = false) middle last)
    (first_marked : mark first.1 = true) (last_marked : mark last.1 = true) :
    NativeFirstReturn table deterministic compatible mark (iota (e := e) first) (iota (e := e) last) := by sorry
