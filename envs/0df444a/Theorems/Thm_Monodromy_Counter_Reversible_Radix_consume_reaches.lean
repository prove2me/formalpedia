-- Prove2me | Theorems.Thm_Monodromy_Counter_Reversible_Radix_consume_reaches
-- name    : Monodromy.Counter.Reversible.Radix.consume_reaches
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:45:00.151899+00:00
-- url     : https://prove2.me/theorems/aec9be45-dd9c-45b1-b778-5938db6d0288
-- title:
--   Radix consumption accumulates the quotient
-- statement:
--   For every positive p, natural input x and accumulator y, and remainder r<p, the reversible radix table has a finite run from block(r,0) with counters (x,y) to block((x+r) mod p,2) with counters (0,y+⌊(x+r)/p⌋). Thus the conclusion keeps the resulting remainder in the finite control phase and does not yet perform the transfer-back stage.
--
--   Statement dependencies: `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.Reversible.Radix.block`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.point`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Radix.table`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`.
--
--   Original proof dependencies: `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.DivMod.residue_small`, `Monodromy.Counter.Reversible.Action`, `Monodromy.Counter.Reversible.Action.apply`, `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Edge.execute`, `Monodromy.Counter.Reversible.Radix.Arc`, `Monodromy.Counter.Reversible.Radix.Node`, `Monodromy.Counter.Reversible.Radix.arcEquiv`, `Monodromy.Counter.Reversible.Radix.block`, `Monodromy.Counter.Reversible.Radix.carry_reaches`, `Monodromy.Counter.Reversible.Radix.consume_step`, `Monodromy.Counter.Reversible.Radix.destination`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.global`, `Monodromy.Counter.Reversible.Radix.move`, `Monodromy.Counter.Reversible.Radix.next`, `Monodromy.Counter.Reversible.Radix.nodeEquiv`, `Monodromy.Counter.Reversible.Radix.operation`, `Monodromy.Counter.Reversible.Radix.origin`, `Monodromy.Counter.Reversible.Radix.point`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Radix.table`, `Monodromy.Counter.Reversible.Radix.table_arc`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.Reversible.Radix.block`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.point`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Radix.table`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.DivMod.residue_small`, `Monodromy.Counter.Reversible.Action`, `Monodromy.Counter.Reversible.Action.apply`, `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Edge.enabled`, `Monodromy.Counter.Reversible.Edge.execute`, `Monodromy.Counter.Reversible.Radix.Arc`, `Monodromy.Counter.Reversible.Radix.Node`, `Monodromy.Counter.Reversible.Radix.arcEquiv`, `Monodromy.Counter.Reversible.Radix.block`, `Monodromy.Counter.Reversible.Radix.carry_reaches`, `Monodromy.Counter.Reversible.Radix.consume_step`, `Monodromy.Counter.Reversible.Radix.destination`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.global`, `Monodromy.Counter.Reversible.Radix.move`, `Monodromy.Counter.Reversible.Radix.next`, `Monodromy.Counter.Reversible.Radix.nodeEquiv`, `Monodromy.Counter.Reversible.Radix.operation`, `Monodromy.Counter.Reversible.Radix.origin`, `Monodromy.Counter.Reversible.Radix.point`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Radix.table`, `Monodromy.Counter.Reversible.Radix.table_arc`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Reversible.Radix.consume_reaches at L4792-L4834 [UTF-8 237823:240579].

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

theorem Monodromy.Counter.Reversible.Radix.consume_reaches (input accumulator : ℕ) (remainder : Fin p) :
    StateTransition.Reaches (step (table p))
      (point p (block p remainder 0) input accumulator)
      (point p (block p (Counter.DivMod.residue p (input + remainder.val)) 2) 0
        (accumulator + (input + remainder.val) / p : ℕ)) := by sorry
