-- Prove2me | Theorems.Thm_Monodromy_ReversibleTuring_step_firstReturn
-- name    : Monodromy.ReversibleTuring.step_firstReturn
-- status  : Open
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:51:50.427946+00:00
-- url     : https://prove2.me/theorems/9afc1ce6-efe7-4fb3-815b-76b7aabd994e
-- title:
--   A Recorded Turing Step Is a Marked First Return with Larger History
-- statement:
--   For positive naturals a,q, a Turing machine m over Fin a and Fin q, complete configurations x,y with TM0.step(m,x)=some y, and any natural history h, there exists a natural h′>h such that the reversible recording table has a positive first return from its encoding of (x,h) to its encoding of (y,h′) at the finite Turing-dispatch marks, with no marked intermediate return.
--
--   Statement dependencies: `Monodromy.Counter.Compression.size`, `Monodromy.Counter.Reversible.Recording.MarkedFirstReturn`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.NativeTuring.counterMark`, `Monodromy.NativeTuring.source2`, `Monodromy.NativeTuring.source3`, `Monodromy.ReversibleTuring.encode`.
--
--   Original proof dependencies: `Monodromy.Counter.Compression.dispatch`, `Monodromy.Counter.Compression.encode`, `Monodromy.Counter.Compression.size`, `Monodromy.Counter.Configuration`, `Monodromy.Counter.Reversible.Recording.MarkedFirstReturn`, `Monodromy.Counter.Reversible.Recording.marked_firstReturn`, `Monodromy.Counter.TuringCompiler.Row`, `Monodromy.Counter.TuringCompiler.dispatch`, `Monodromy.Counter.TuringCompiler.encode`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.Counter.step`, `Monodromy.NativeTuring.CounterInternalReaches`, `Monodromy.NativeTuring.CounterInternalStep`, `Monodromy.NativeTuring.CounterMarked`, `Monodromy.NativeTuring.counterMark`, `Monodromy.NativeTuring.counter_firstReturn`, `Monodromy.NativeTuring.source2`, `Monodromy.NativeTuring.source3`, `Monodromy.RecordedTuring.counterEncode`, `Monodromy.RecordedTuring.size`, `Monodromy.ReversibleTuring.encode`, `Monodromy.ReversibleTuring.source_marked`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Compression.size`, `Monodromy.Counter.Reversible.Recording.MarkedFirstReturn`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.NativeTuring.counterMark`, `Monodromy.NativeTuring.source2`, `Monodromy.NativeTuring.source3`, `Monodromy.ReversibleTuring.encode`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Compression.dispatch`, `Monodromy.Counter.Compression.encode`, `Monodromy.Counter.Compression.size`, `Monodromy.Counter.Configuration`, `Monodromy.Counter.Reversible.Recording.MarkedFirstReturn`, `Monodromy.Counter.Reversible.Recording.marked_firstReturn`, `Monodromy.Counter.TuringCompiler.Row`, `Monodromy.Counter.TuringCompiler.dispatch`, `Monodromy.Counter.TuringCompiler.encode`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.Counter.step`, `Monodromy.NativeTuring.CounterInternalReaches`, `Monodromy.NativeTuring.CounterInternalStep`, `Monodromy.NativeTuring.CounterMarked`, `Monodromy.NativeTuring.counterMark`, `Monodromy.NativeTuring.counter_firstReturn`, `Monodromy.NativeTuring.source2`, `Monodromy.NativeTuring.source3`, `Monodromy.RecordedTuring.counterEncode`, `Monodromy.RecordedTuring.size`, `Monodromy.ReversibleTuring.encode`, `Monodromy.ReversibleTuring.source_marked`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/FormalCompilation.lean (file SHA-256 c07335814044367fc4605d1e494fe82a30c684f754d58d55aaa7514b94c37122):
--   Monodromy.ReversibleTuring.step_firstReturn at L841-L861 [UTF-8 42765:44215].

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
open Monodromy.ReversibleTuring
open Turing
variable (a q : ℕ) [NeZero a] [NeZero q]

theorem Monodromy.ReversibleTuring.step_firstReturn (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      Counter.Reversible.Recording.MarkedFirstReturn (NativeTuring.source2 a q machine)
        (NativeTuring.counterMark a q machine)
        (encode a q machine first history) (encode a q machine last finalHistory) := by sorry
