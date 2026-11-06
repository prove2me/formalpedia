-- Prove2me | Theorems.Thm_Monodromy_Counter_Reversible_Radix_reaches_result
-- name    : Monodromy.Counter.Reversible.Radix.reaches_result
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:47:12.793825+00:00
-- url     : https://prove2.me/theorems/8b0185ba-6be9-493e-b075-5e9efbae7acb
-- title:
--   The reversible radix table computes quotient and remainder
-- statement:
--   For every positive radix p and natural input x, the fixed reversible two-counter table has a finite run from entry with counters (x,0) to finish(x mod p) with counters (⌊x/p⌋,0). The remainder is the finish-port index; the quotient occupies the first counter and the workspace is zero. This is a reachability assertion, including x=0.
--
--   Statement dependencies: `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.entry`, `Monodromy.Counter.Reversible.Radix.finish`, `Monodromy.Counter.Reversible.Radix.point`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Radix.table`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`.
--
--   Original proof dependencies: `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.Reversible.Action`, `Monodromy.Counter.Reversible.Action.apply`, `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Edge.execute`, `Monodromy.Counter.Reversible.Radix.Arc`, `Monodromy.Counter.Reversible.Radix.Node`, `Monodromy.Counter.Reversible.Radix.arcEquiv`, `Monodromy.Counter.Reversible.Radix.block`, `Monodromy.Counter.Reversible.Radix.consume_reaches`, `Monodromy.Counter.Reversible.Radix.destination`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.entry`, `Monodromy.Counter.Reversible.Radix.finish`, `Monodromy.Counter.Reversible.Radix.move`, `Monodromy.Counter.Reversible.Radix.nodeEquiv`, `Monodromy.Counter.Reversible.Radix.operation`, `Monodromy.Counter.Reversible.Radix.origin`, `Monodromy.Counter.Reversible.Radix.point`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Radix.table`, `Monodromy.Counter.Reversible.Radix.table_arc`, `Monodromy.Counter.Reversible.Radix.transfer_reaches`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.entry`, `Monodromy.Counter.Reversible.Radix.finish`, `Monodromy.Counter.Reversible.Radix.point`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Radix.table`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.Reversible.Action`, `Monodromy.Counter.Reversible.Action.apply`, `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Edge.enabled`, `Monodromy.Counter.Reversible.Edge.execute`, `Monodromy.Counter.Reversible.Radix.Arc`, `Monodromy.Counter.Reversible.Radix.Node`, `Monodromy.Counter.Reversible.Radix.arcEquiv`, `Monodromy.Counter.Reversible.Radix.block`, `Monodromy.Counter.Reversible.Radix.consume_reaches`, `Monodromy.Counter.Reversible.Radix.destination`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.entry`, `Monodromy.Counter.Reversible.Radix.finish`, `Monodromy.Counter.Reversible.Radix.global`, `Monodromy.Counter.Reversible.Radix.move`, `Monodromy.Counter.Reversible.Radix.nodeEquiv`, `Monodromy.Counter.Reversible.Radix.operation`, `Monodromy.Counter.Reversible.Radix.origin`, `Monodromy.Counter.Reversible.Radix.point`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Radix.table`, `Monodromy.Counter.Reversible.Radix.table_arc`, `Monodromy.Counter.Reversible.Radix.transfer_reaches`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Reversible.Radix.reaches_result at L4888-L4907 [UTF-8 243864:245272].

module
public import Definitions.Def_Monodromy_Counter
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
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
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
open Monodromy.Counter
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.Radix
variable (p : ℕ) [NeZero p]

theorem Monodromy.Counter.Reversible.Radix.reaches_result (input : ℕ) :
    StateTransition.Reaches (step (table p)) (point p (entry p) input 0)
      (point p (finish p (Counter.DivMod.residue p input)) (input / p : ℕ) 0) := by sorry
