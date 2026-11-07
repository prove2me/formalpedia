-- Prove2me | Theorems.Thm_Monodromy_ReversibleNativeTuring_step_firstReturn
-- name    : Monodromy.ReversibleNativeTuring.step_firstReturn
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:52:58.439632+00:00
-- url     : https://prove2.me/theorems/4fcf533c-f916-4fb9-824c-6fccab9ac5ff
-- title:
--   A Live Turing Step Is the Next Marked Native Word Return
-- statement:
--   For positive naturals a,q, a Turing machine m over Fin a and Fin q, complete configurations x,y with TM0.step(m,x)=some y, and any natural history h, there exists h′>h such that the selected reversible native program has a positive first return from I(x,h) to I(y,h′). Both endpoints satisfy its finite-root boundary observation, and all intermediate native step departures after the first lie outside that boundary.
--
--   Statement dependencies: `Monodromy.ReversibleNativeTuring.FirstReturn`, `Monodromy.ReversibleNativeTuring.iota`.
--
--   Original proof dependencies: `Monodromy.Counter.Compression.size`, `Monodromy.Counter.Reversible.PrimeCompression.InternalMarkedReaches`, `Monodromy.Counter.Reversible.PrimeCompression.InternalMarkedStep`, `Monodromy.Counter.Reversible.PrimeCompression.Marked`, `Monodromy.Counter.Reversible.PrimeCompression.MarkedFirstReturn`, `Monodromy.Counter.Reversible.PrimeCompression.rawEdges`, `Monodromy.Counter.Reversible.PrimeCompression.size`, `Monodromy.Counter.Reversible.PrimeCompression.table`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.NativeTuring.source2`, `Monodromy.NativeTuring.source3`, `Monodromy.RecordedTuring.size`, `Monodromy.ReversibleCompilation.marked_firstReturn`, `Monodromy.ReversibleNativeTuring.FirstReturn`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.size_nonzero`, `Monodromy.ReversibleTuring.Compression.Boundary`, `Monodromy.ReversibleTuring.Compression.basis`, `Monodromy.ReversibleTuring.Compression.deterministic`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.encode`, `Monodromy.ReversibleTuring.Compression.mark`, `Monodromy.ReversibleTuring.Compression.mark_false_iff`, `Monodromy.ReversibleTuring.Compression.mark_true_iff`, `Monodromy.ReversibleTuring.Compression.size`, `Monodromy.ReversibleTuring.Compression.sourceMark`, `Monodromy.ReversibleTuring.Compression.source_deterministic`, `Monodromy.ReversibleTuring.Compression.source_targetCompatible`, `Monodromy.ReversibleTuring.Compression.step_firstReturn`, `Monodromy.ReversibleTuring.Compression.table`, `Monodromy.ReversibleTuring.Compression.targetCompatible`, `Monodromy.ReversibleTuring.table`.
--
--   Statement elaboration dependencies: `Monodromy.ReversibleNativeTuring.FirstReturn`, `Monodromy.ReversibleNativeTuring.iota`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Compression.size`, `Monodromy.Counter.Reversible.PrimeCompression.InternalMarkedReaches`, `Monodromy.Counter.Reversible.PrimeCompression.InternalMarkedStep`, `Monodromy.Counter.Reversible.PrimeCompression.Marked`, `Monodromy.Counter.Reversible.PrimeCompression.MarkedFirstReturn`, `Monodromy.Counter.Reversible.PrimeCompression.rawEdges`, `Monodromy.Counter.Reversible.PrimeCompression.size`, `Monodromy.Counter.Reversible.PrimeCompression.table`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.NativeTuring.source2`, `Monodromy.NativeTuring.source3`, `Monodromy.RecordedTuring.size`, `Monodromy.ReversibleCompilation.marked_firstReturn`, `Monodromy.ReversibleNativeTuring.FirstReturn`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.size_nonzero`, `Monodromy.ReversibleTuring.Compression.Boundary`, `Monodromy.ReversibleTuring.Compression.basis`, `Monodromy.ReversibleTuring.Compression.deterministic`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.encode`, `Monodromy.ReversibleTuring.Compression.mark`, `Monodromy.ReversibleTuring.Compression.mark_false_iff`, `Monodromy.ReversibleTuring.Compression.mark_true_iff`, `Monodromy.ReversibleTuring.Compression.size`, `Monodromy.ReversibleTuring.Compression.sourceMark`, `Monodromy.ReversibleTuring.Compression.source_deterministic`, `Monodromy.ReversibleTuring.Compression.source_targetCompatible`, `Monodromy.ReversibleTuring.Compression.step_firstReturn`, `Monodromy.ReversibleTuring.Compression.table`, `Monodromy.ReversibleTuring.Compression.targetCompatible`, `Monodromy.ReversibleTuring.table`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/FormalCompilation.lean (file SHA-256 c07335814044367fc4605d1e494fe82a30c684f754d58d55aaa7514b94c37122):
--   Monodromy.ReversibleNativeTuring.step_firstReturn at L1373-L1393 [UTF-8 72279:73720].

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
open Monodromy.ReversibleNativeTuring
open Turing CoupledContinuation ReversibleTuring
variable (a q : ℕ) [NeZero a] [NeZero q]

theorem Monodromy.ReversibleNativeTuring.step_firstReturn (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      FirstReturn a q machine (iota a q machine first history) (iota a q machine last finalHistory) := by sorry
