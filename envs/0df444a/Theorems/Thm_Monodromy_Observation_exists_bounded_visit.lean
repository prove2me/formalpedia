-- Prove2me | Theorems.Thm_Monodromy_Observation_exists_bounded_visit
-- name    : Monodromy.Observation.exists_bounded_visit
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:37:27.96567+00:00
-- url     : https://prove2.me/theorems/ebbe3969-6686-4f28-9b60-8045b00454b9
-- title:
--   A Visit in a Finite Orbit Occurs Before the Number of States
-- statement:
--   For any finite type S with its Fintype enumeration, map A:S→S, Boolean test b:S→Bool and state s∈S, assume b(Aⁿ(s)) is true for some natural n. Then it is true for some natural n strictly smaller than |S|. The conclusion permits n=0 and does not require A to be injective.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Observation.lean (file SHA-256 7989443c07eb69c1a560c79f678d827f7e8efd3f352ab0119eebb2cac76505bd):
--   Monodromy.Observation.exists_bounded_visit at L93-L117 [UTF-8 4079:5574].

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

theorem Monodromy.Observation.exists_bounded_visit [Fintype S] (next : S → S) (visit : S → Bool) (state : S)
    (eventually : ∃ rounds : ℕ, visit ((next^[rounds]) state) = true) :
    ∃ rounds < Fintype.card S, visit ((next^[rounds]) state) = true := by sorry
