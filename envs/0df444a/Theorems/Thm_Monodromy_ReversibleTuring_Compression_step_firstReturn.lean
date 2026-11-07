-- Prove2me | Theorems.Thm_Monodromy_ReversibleTuring_Compression_step_firstReturn
-- name    : Monodromy.ReversibleTuring.Compression.step_firstReturn
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:52:13.510212+00:00
-- url     : https://prove2.me/theorems/8fe27681-a2aa-4a8a-9db6-ec3f58bce911
-- title:
--   Prime Compression Preserves the Marked Turing Step and Its Growing History
-- statement:
--   For positive naturals a,q, a Turing machine m over Fin a and Fin q, configurations x,y with TM0.step(m,x)=some y, and any natural history h, there exists h′>h such that the fixed prime compression of the four-register recording table has a marked positive first return from encode(x,h) to encode(y,h′). The marks are the specified source Turing-dispatch boundaries, and no intermediate compressed return is marked.
--
--   Statement dependencies: `Monodromy.Counter.Compression.size`, `Monodromy.Counter.Reversible.PrimeCompression.MarkedFirstReturn`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.NativeTuring.source2`, `Monodromy.NativeTuring.source3`, `Monodromy.RecordedTuring.size`, `Monodromy.ReversibleTuring.Compression.basis`, `Monodromy.ReversibleTuring.Compression.encode`, `Monodromy.ReversibleTuring.Compression.sourceMark`, `Monodromy.ReversibleTuring.Compression.source_deterministic`, `Monodromy.ReversibleTuring.Compression.source_targetCompatible`, `Monodromy.ReversibleTuring.table`.
--
--   Original proof dependencies: `Monodromy.Counter.Compression.size`, `Monodromy.Counter.Reversible.PrimeCompression.MarkedFirstReturn`, `Monodromy.Counter.Reversible.PrimeCompression.encode`, `Monodromy.Counter.Reversible.PrimeCompression.marked_firstReturn`, `Monodromy.Counter.Reversible.PrimeCompression.toNatural`, `Monodromy.Counter.Reversible.Recording.InternalMarkedReaches`, `Monodromy.Counter.Reversible.Recording.InternalMarkedStep`, `Monodromy.Counter.Reversible.Recording.Marked`, `Monodromy.Counter.Reversible.Recording.MarkedFirstReturn`, `Monodromy.Counter.Reversible.Recording.Valid`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.stable`, `Monodromy.Counter.Reversible.Recording.table`, `Monodromy.Counter.Reversible.Recording.unitShift`, `Monodromy.Counter.Reversible.Recording.valid_encode`, `Monodromy.Counter.Reversible.Recording.valid_nonnegative`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.NativeTuring.counterMark`, `Monodromy.NativeTuring.source2`, `Monodromy.NativeTuring.source3`, `Monodromy.RecordedTuring.counterEncode`, `Monodromy.RecordedTuring.size`, `Monodromy.ReversibleTuring.Boundary`, `Monodromy.ReversibleTuring.Compression.basis`, `Monodromy.ReversibleTuring.Compression.encode`, `Monodromy.ReversibleTuring.Compression.sourceMark`, `Monodromy.ReversibleTuring.Compression.sourceMark_false_iff`, `Monodromy.ReversibleTuring.Compression.sourceMark_true_iff`, `Monodromy.ReversibleTuring.Compression.source_deterministic`, `Monodromy.ReversibleTuring.Compression.source_targetCompatible`, `Monodromy.ReversibleTuring.encode`, `Monodromy.ReversibleTuring.step_firstReturn`, `Monodromy.ReversibleTuring.table`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Compression.size`, `Monodromy.Counter.Reversible.PrimeCompression.MarkedFirstReturn`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.NativeTuring.source2`, `Monodromy.NativeTuring.source3`, `Monodromy.RecordedTuring.size`, `Monodromy.ReversibleTuring.Compression.basis`, `Monodromy.ReversibleTuring.Compression.encode`, `Monodromy.ReversibleTuring.Compression.sourceMark`, `Monodromy.ReversibleTuring.Compression.source_deterministic`, `Monodromy.ReversibleTuring.Compression.source_targetCompatible`, `Monodromy.ReversibleTuring.table`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Compression.size`, `Monodromy.Counter.Reversible.PrimeCompression.MarkedFirstReturn`, `Monodromy.Counter.Reversible.PrimeCompression.encode`, `Monodromy.Counter.Reversible.PrimeCompression.marked_firstReturn`, `Monodromy.Counter.Reversible.PrimeCompression.toNatural`, `Monodromy.Counter.Reversible.Recording.InternalMarkedReaches`, `Monodromy.Counter.Reversible.Recording.InternalMarkedStep`, `Monodromy.Counter.Reversible.Recording.Marked`, `Monodromy.Counter.Reversible.Recording.MarkedFirstReturn`, `Monodromy.Counter.Reversible.Recording.Valid`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.stable`, `Monodromy.Counter.Reversible.Recording.table`, `Monodromy.Counter.Reversible.Recording.unitShift`, `Monodromy.Counter.Reversible.Recording.valid_encode`, `Monodromy.Counter.Reversible.Recording.valid_nonnegative`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.NativeTuring.counterMark`, `Monodromy.NativeTuring.source2`, `Monodromy.NativeTuring.source3`, `Monodromy.RecordedTuring.counterEncode`, `Monodromy.RecordedTuring.size`, `Monodromy.ReversibleTuring.Boundary`, `Monodromy.ReversibleTuring.Compression.basis`, `Monodromy.ReversibleTuring.Compression.encode`, `Monodromy.ReversibleTuring.Compression.sourceMark`, `Monodromy.ReversibleTuring.Compression.sourceMark_false_iff`, `Monodromy.ReversibleTuring.Compression.sourceMark_true_iff`, `Monodromy.ReversibleTuring.Compression.source_deterministic`, `Monodromy.ReversibleTuring.Compression.source_targetCompatible`, `Monodromy.ReversibleTuring.encode`, `Monodromy.ReversibleTuring.step_firstReturn`, `Monodromy.ReversibleTuring.table`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/FormalCompilation.lean (file SHA-256 c07335814044367fc4605d1e494fe82a30c684f754d58d55aaa7514b94c37122):
--   Monodromy.ReversibleTuring.Compression.step_firstReturn at L1171-L1203 [UTF-8 60925:63170].

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
open Monodromy.ReversibleTuring.Compression
open Turing Counter.Reversible
variable (a q : ℕ) [NeZero a] [NeZero q]

theorem Monodromy.ReversibleTuring.Compression.step_firstReturn (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      PrimeCompression.MarkedFirstReturn basis (ReversibleTuring.table a q machine)
        (source_deterministic a q machine) (source_targetCompatible a q machine)
        (sourceMark a q machine)
        (Monodromy.ReversibleTuring.Compression.encode a q machine first history) (Monodromy.ReversibleTuring.Compression.encode a q machine last finalHistory) := by sorry
