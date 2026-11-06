-- Prove2me | Theorems.Thm_Monodromy_FormalCompilation_eval1
-- name    : Monodromy.FormalCompilation.eval1
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:43:00.50694+00:00
-- url     : https://prove2.me/theorems/cdaad629-8e11-40fb-8ed4-4b9b9ce259fc
-- title:
--   Stack-to-Tape Translation Preserves the Entire Partial Evaluation
-- statement:
--   For every source ToPartrec code and every finite list v of natural-number arguments, the translated TM1 machine’s partial evaluation from its initial tapeData(v) configuration equals source.eval(v) with each returned list mapped to the specified halted TM1 configuration halt1(source,·). The equality includes the undefined case and also applies to the empty argument list.
--
--   Statement dependencies: `Monodromy.FormalCompilation.Alphabet`, `Monodromy.FormalCompilation.Control1`, `Monodromy.FormalCompilation.Stack`, `Monodromy.FormalCompilation.Store`, `Monodromy.FormalCompilation.Symbol`, `Monodromy.FormalCompilation.control1Inhabited`, `Monodromy.FormalCompilation.halt1`, `Monodromy.FormalCompilation.machine1`, `Monodromy.FormalCompilation.tapeData`.
--
--   Original proof dependencies: `Monodromy.FormalCompilation.Alphabet`, `Monodromy.FormalCompilation.Control1`, `Monodromy.FormalCompilation.Stack`, `Monodromy.FormalCompilation.Store`, `Monodromy.FormalCompilation.Symbol`, `Monodromy.FormalCompilation.control1Inhabited`, `Monodromy.FormalCompilation.halt1`, `Monodromy.FormalCompilation.halt_relation`, `Monodromy.FormalCompilation.initial_relation`, `Monodromy.FormalCompilation.machine1`, `Monodromy.FormalCompilation.relation_unique`, `Monodromy.FormalCompilation.tapeData`.
--
--   Statement elaboration dependencies: `Monodromy.FormalCompilation.Alphabet`, `Monodromy.FormalCompilation.Control1`, `Monodromy.FormalCompilation.Stack`, `Monodromy.FormalCompilation.Store`, `Monodromy.FormalCompilation.Symbol`, `Monodromy.FormalCompilation.control1Inhabited`, `Monodromy.FormalCompilation.halt1`, `Monodromy.FormalCompilation.machine1`, `Monodromy.FormalCompilation.tapeData`.
--
--   Proof elaboration dependencies: `Monodromy.FormalCompilation.Alphabet`, `Monodromy.FormalCompilation.Control1`, `Monodromy.FormalCompilation.Stack`, `Monodromy.FormalCompilation.Store`, `Monodromy.FormalCompilation.Symbol`, `Monodromy.FormalCompilation.control1Inhabited`, `Monodromy.FormalCompilation.halt1`, `Monodromy.FormalCompilation.halt_relation`, `Monodromy.FormalCompilation.initial_relation`, `Monodromy.FormalCompilation.machine1`, `Monodromy.FormalCompilation.relation_unique`, `Monodromy.FormalCompilation.tapeData`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/FormalCompilation.lean (file SHA-256 c07335814044367fc4605d1e494fe82a30c684f754d58d55aaa7514b94c37122):
--   Monodromy.FormalCompilation.eval1 at L128-L154 [UTF-8 5318:6816].

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

theorem Monodromy.FormalCompilation.eval1 (values : List ℕ) :
    StateTransition.eval (TM1.step (machine1 source))
      (TM1.init (tapeData values) : TM1.Cfg Alphabet (Control1 source) Store) =
      halt1 source <$> source.eval values := by sorry
