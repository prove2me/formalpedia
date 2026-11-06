-- Prove2me | Theorems.Thm_Monodromy_ReversibleTuring_macroStep_live
-- name    : Monodromy.ReversibleTuring.macroStep_live
-- status  : Open
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:52:28.359196+00:00
-- url     : https://prove2.me/theorems/6ca612e6-1af6-4d79-813a-d9048d93256d
-- title:
--   The Recorded Macro Executes a Live Turing Step and Retains Its New History
-- statement:
--   For positive naturals a,q, a Turing machine m over Fin a and Fin q, configurations x,y satisfying TM0.step(m,x)=some y, and every natural history h, there is a natural h′>h for which the recorded table’s causal marked-return macro at encode(x,h) is defined with optional value some encode(y,h′). The complete successor configuration and the strictly larger retained history use the same witness h′.
--
--   Statement dependencies: `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.State`, `Monodromy.RecordedTuring.size`, `Monodromy.ReversibleTuring.encode`, `Monodromy.ReversibleTuring.macroStep`.
--
--   Original proof dependencies: `Monodromy.Counter.Compression.size`, `Monodromy.Counter.Reversible.Recording.InternalMarkedReaches`, `Monodromy.Counter.Reversible.Recording.Marked`, `Monodromy.Counter.Reversible.Recording.MarkedFirstReturn`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.table`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.NativeTuring.counterMark`, `Monodromy.NativeTuring.source2`, `Monodromy.NativeTuring.source3`, `Monodromy.RecordedTuring.size`, `Monodromy.ReversibleTuring.boundaryTransition`, `Monodromy.ReversibleTuring.boundaryTransition_stops`, `Monodromy.ReversibleTuring.encode`, `Monodromy.ReversibleTuring.internal_marked_reaches`, `Monodromy.ReversibleTuring.macroStep`, `Monodromy.ReversibleTuring.step_firstReturn`, `Monodromy.ReversibleTuring.table`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.State`, `Monodromy.RecordedTuring.size`, `Monodromy.ReversibleTuring.encode`, `Monodromy.ReversibleTuring.macroStep`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Compression.size`, `Monodromy.Counter.Reversible.Recording.InternalMarkedReaches`, `Monodromy.Counter.Reversible.Recording.Marked`, `Monodromy.Counter.Reversible.Recording.MarkedFirstReturn`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.table`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.NativeTuring.counterMark`, `Monodromy.NativeTuring.source2`, `Monodromy.NativeTuring.source3`, `Monodromy.RecordedTuring.size`, `Monodromy.ReversibleTuring.boundaryTransition`, `Monodromy.ReversibleTuring.boundaryTransition_stops`, `Monodromy.ReversibleTuring.encode`, `Monodromy.ReversibleTuring.internal_marked_reaches`, `Monodromy.ReversibleTuring.macroStep`, `Monodromy.ReversibleTuring.step_firstReturn`, `Monodromy.ReversibleTuring.table`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/FormalCompilation.lean (file SHA-256 c07335814044367fc4605d1e494fe82a30c684f754d58d55aaa7514b94c37122):
--   Monodromy.ReversibleTuring.macroStep_live at L925-L942 [UTF-8 47811:48917].

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

theorem Monodromy.ReversibleTuring.macroStep_live (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      macroStep a q machine (encode a q machine first history) =
        Part.some (some (encode a q machine last finalHistory)) := by sorry
