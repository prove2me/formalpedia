-- Prove2me | Theorems.Thm_Monodromy_FormalCompilation_relation_unique
-- name    : Monodromy.FormalCompilation.relation_unique
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:36:43.81348+00:00
-- url     : https://prove2.me/theorems/5d3a57ea-6b8f-4db8-93e0-4f8e43466d85
-- title:
--   A Stack Configuration Determines Its Related Packed Tape Configuration
-- statement:
--   For any source ToPartrec code, any configuration of the associated four-stack TM2 representation, and any two configurations of the associated TM1 tape representation, if both TM1 configurations are related to that same TM2 configuration by Mathlib’s stack-to-tape configuration relation TrCfg, then the two TM1 configurations are equal, including control, store and packed tape.
--
--   Statement dependencies: `Monodromy.FormalCompilation.Alphabet`, `Monodromy.FormalCompilation.Control1`, `Monodromy.FormalCompilation.Label2`, `Monodromy.FormalCompilation.Stack`, `Monodromy.FormalCompilation.Store`, `Monodromy.FormalCompilation.Symbol`.
--
--   Original proof dependencies: `Monodromy.FormalCompilation.Alphabet`, `Monodromy.FormalCompilation.Control1`, `Monodromy.FormalCompilation.Label2`, `Monodromy.FormalCompilation.Stack`, `Monodromy.FormalCompilation.Store`, `Monodromy.FormalCompilation.Symbol`.
--
--   Statement elaboration dependencies: `Monodromy.FormalCompilation.Alphabet`, `Monodromy.FormalCompilation.Control1`, `Monodromy.FormalCompilation.Label2`, `Monodromy.FormalCompilation.Stack`, `Monodromy.FormalCompilation.Store`, `Monodromy.FormalCompilation.Symbol`.
--
--   Proof elaboration dependencies: `Monodromy.FormalCompilation.Alphabet`, `Monodromy.FormalCompilation.Control1`, `Monodromy.FormalCompilation.Label2`, `Monodromy.FormalCompilation.Stack`, `Monodromy.FormalCompilation.Store`, `Monodromy.FormalCompilation.Symbol`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/FormalCompilation.lean (file SHA-256 c07335814044367fc4605d1e494fe82a30c684f754d58d55aaa7514b94c37122):
--   Monodromy.FormalCompilation.relation_unique at L93-L111 [UTF-8 3724:4586].

module
public import Definitions.Def_Monodromy_FormalCompilation
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Computability.TuringMachine.ToPartrec
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

open Monodromy
open Monodromy.FormalCompilation
open Turing
variable (source : ToPartrec.Code)

theorem Monodromy.FormalCompilation.relation_unique
    {configuration : TM2.Cfg (fun _ : Stack => Symbol) Label2 Store}
    {first second : TM1.Cfg Alphabet (Control1 source) Store}
    (first_related : TM2to1.TrCfg configuration first)
    (second_related : TM2to1.TrCfg configuration second) : first = second := by sorry
