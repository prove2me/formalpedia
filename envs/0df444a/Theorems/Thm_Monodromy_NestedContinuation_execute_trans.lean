-- Prove2me | Theorems.Thm_Monodromy_NestedContinuation_execute_trans
-- name    : Monodromy.NestedContinuation.execute_trans
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:43:41.115131+00:00
-- url     : https://prove2.me/theorems/49062738-e9b4-4b78-8d3b-11eaad199904
-- title:
--   Concatenated Nested Lifts Execute in Path Order
-- statement:
--   For any two loops α,β in the punctured complex plane based at exp(1), each avoiding the point 1 at every time, and any state z in the nested exponential fiber exp(exp(z))=exp(1), actual nested execution along α concatenated with β equals execution along β from the state obtained by first executing α. The avoidance proof for the concatenated path is the one induced by the two given hypotheses.
--
--   Statement dependencies: `Monodromy.NestedContinuation.Memory`, `Monodromy.NestedContinuation.Punctured`, `Monodromy.NestedContinuation.avoids_trans`, `Monodromy.NestedContinuation.base`, `Monodromy.NestedContinuation.execute`.
--
--   Original proof dependencies: `Monodromy.NestedContinuation.Memory`, `Monodromy.NestedContinuation.Punctured`, `Monodromy.NestedContinuation.avoids_trans`, `Monodromy.NestedContinuation.base`, `Monodromy.NestedContinuation.execute`, `Monodromy.NestedContinuation.expCover`, `Monodromy.NestedContinuation.nested_curve_unique`, `Monodromy.NestedContinuation.secondRaw`, `Monodromy.NestedContinuation.secondRaw_projects`, `Monodromy.NestedContinuation.secondRaw_start`, `Monodromy.NestedContinuation.sequentialPath`, `Monodromy.NestedContinuation.sequentialPath_projects`.
--
--   Statement elaboration dependencies: `Monodromy.NestedContinuation.Memory`, `Monodromy.NestedContinuation.Punctured`, `Monodromy.NestedContinuation.avoids_trans`, `Monodromy.NestedContinuation.base`, `Monodromy.NestedContinuation.execute`.
--
--   Proof elaboration dependencies: `Monodromy.NestedContinuation.Memory`, `Monodromy.NestedContinuation.Punctured`, `Monodromy.NestedContinuation.avoids_trans`, `Monodromy.NestedContinuation.base`, `Monodromy.NestedContinuation.execute`, `Monodromy.NestedContinuation.expCover`, `Monodromy.NestedContinuation.nested_curve_unique`, `Monodromy.NestedContinuation.secondRaw`, `Monodromy.NestedContinuation.secondRaw_projects`, `Monodromy.NestedContinuation.secondRaw_start`, `Monodromy.NestedContinuation.sequentialPath`, `Monodromy.NestedContinuation.sequentialPath_projects`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Logarithm.lean (file SHA-256 7c717767a34b9975b34b033cf81fed276c1e642f6bb7abceab23baba8a3ee1d1):
--   Monodromy.NestedContinuation.execute_trans at L574-L590 [UTF-8 26103:27305].

module
public import Definitions.Def_Monodromy_Logarithm
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

open Monodromy
open Monodromy.NestedContinuation
open unitInterval

theorem Monodromy.NestedContinuation.execute_trans (first second : Path base base)
    (first_avoids : ∀ t, first t ≠ (⟨1, one_ne_zero⟩ : Punctured))
    (second_avoids : ∀ t, second t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    execute (first.trans second) (avoids_trans first second first_avoids second_avoids) state =
      execute second second_avoids (execute first first_avoids state) := by sorry
