-- Prove2me | Theorems.Thm_Monodromy_Counter_Reversible_PrimeCompression_test_firstReturn
-- name    : Monodromy.Counter.Reversible.PrimeCompression.test_firstReturn
-- status  : Open
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:48:49.053266+00:00
-- url     : https://prove2.me/theorems/1800a54e-febd-4721-ba8d-4183abc4d04b
-- title:
--   An enabled source test has a compressed first return
-- statement:
--   For arbitrary natural n,q,e, distinct-prime basis and source table with complementary same-register tests at shared source or target vertices, let edge j start at a natural configuration u and test register k with Boolean flag b. Assume the test is enabled on the integer casts of u’s counters: the selected counter is zero exactly when b=true. The prime-compressed two-counter table has a first return to j’s target with every source counter unchanged, with both endpoints at retained source boundaries and no intermediate source-boundary departure state.
--
--   Statement dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Reversible.Action`, `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.PrimeCompression.FirstReturn`, `Monodromy.Counter.Reversible.PrimeCompression.encode`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.PrimeCode.Basis`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.Reversible.Action`, `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.PortNetwork.control`, `Monodromy.Counter.Reversible.PortNetwork.size`, `Monodromy.Counter.Reversible.PrimeCompression.Boundary`, `Monodromy.Counter.Reversible.PrimeCompression.FirstReturn`, `Monodromy.Counter.Reversible.PrimeCompression.HasRestore`, `Monodromy.Counter.Reversible.PrimeCompression.InternalReaches`, `Monodromy.Counter.Reversible.PrimeCompression.InternalStep`, `Monodromy.Counter.Reversible.PrimeCompression.MappedState`, `Monodromy.Counter.Reversible.PrimeCompression.RestoreSite`, `Monodromy.Counter.Reversible.PrimeCompression.SourceSite`, `Monodromy.Counter.Reversible.PrimeCompression.boundary`, `Monodromy.Counter.Reversible.PrimeCompression.boundary_encode`, `Monodromy.Counter.Reversible.PrimeCompression.boundary_source`, `Monodromy.Counter.Reversible.PrimeCompression.componentTable`, `Monodromy.Counter.Reversible.PrimeCompression.connection_controls`, `Monodromy.Counter.Reversible.PrimeCompression.encode`, `Monodromy.Counter.Reversible.PrimeCompression.forward_query_local_positive`, `Monodromy.Counter.Reversible.PrimeCompression.instNeZeroNatModulus`, `Monodromy.Counter.Reversible.PrimeCompression.moduleNode`, `Monodromy.Counter.Reversible.PrimeCompression.moduleRegister`, `Monodromy.Counter.Reversible.PrimeCompression.modulus`, `Monodromy.Counter.Reversible.PrimeCompression.rawEdges`, `Monodromy.Counter.Reversible.PrimeCompression.rawSize`, `Monodromy.Counter.Reversible.PrimeCompression.rawTable`, `Monodromy.Counter.Reversible.PrimeCompression.residue_zero_flag`, `Monodromy.Counter.Reversible.PrimeCompression.restoreInput`, `Monodromy.Counter.Reversible.PrimeCompression.restoreOfTest`, `Monodromy.Counter.Reversible.PrimeCompression.restoreOutput`, `Monodromy.Counter.Reversible.PrimeCompression.restoreRegister_of_test`, `Monodromy.Counter.Reversible.PrimeCompression.restore_connected`, `Monodromy.Counter.Reversible.PrimeCompression.restore_internal_reaches`, `Monodromy.Counter.Reversible.PrimeCompression.restore_pack_local_positive`, `Monodromy.Counter.Reversible.PrimeCompression.reversed`, `Monodromy.Counter.Reversible.PrimeCompression.siteOfEdge`, `Monodromy.Counter.Reversible.PrimeCompression.size`, `Monodromy.Counter.Reversible.PrimeCompression.sourceEdge`, `Monodromy.Counter.Reversible.PrimeCompression.sourceForm_of_test`, `Monodromy.Counter.Reversible.PrimeCompression.sourceInput`, `Monodromy.Counter.Reversible.PrimeCompression.sourceInputPosition`, `Monodromy.Counter.Reversible.PrimeCompression.sourceRegister_of_test`, `Monodromy.Counter.Reversible.PrimeCompression.source_departure`, `Monodromy.Counter.Reversible.PrimeCompression.table`, `Monodromy.Counter.Reversible.PrimeCompression.test_connected`, `Monodromy.Counter.Reversible.PrimeCompression.wiring`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.entry`, `Monodromy.Counter.Reversible.Radix.finish`, `Monodromy.Counter.Reversible.Radix.point`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.Counter.Reversible.step`, `Monodromy.PrimeCode.Basis`, `Monodromy.PrimeCode.Basis.encode`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Reversible.Action`, `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.PrimeCompression.FirstReturn`, `Monodromy.Counter.Reversible.PrimeCompression.encode`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.PrimeCode.Basis`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.Reversible.Action`, `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Glue.mapState`, `Monodromy.Counter.Reversible.PortNetwork.control`, `Monodromy.Counter.Reversible.PortNetwork.size`, `Monodromy.Counter.Reversible.PrimeCompression.Boundary`, `Monodromy.Counter.Reversible.PrimeCompression.FirstReturn`, `Monodromy.Counter.Reversible.PrimeCompression.HasRestore`, `Monodromy.Counter.Reversible.PrimeCompression.InternalReaches`, `Monodromy.Counter.Reversible.PrimeCompression.InternalStep`, `Monodromy.Counter.Reversible.PrimeCompression.MappedState`, `Monodromy.Counter.Reversible.PrimeCompression.RestoreSite`, `Monodromy.Counter.Reversible.PrimeCompression.SourceSite`, `Monodromy.Counter.Reversible.PrimeCompression.boundary`, `Monodromy.Counter.Reversible.PrimeCompression.boundary_encode`, `Monodromy.Counter.Reversible.PrimeCompression.boundary_source`, `Monodromy.Counter.Reversible.PrimeCompression.componentTable`, `Monodromy.Counter.Reversible.PrimeCompression.connection_controls`, `Monodromy.Counter.Reversible.PrimeCompression.encode`, `Monodromy.Counter.Reversible.PrimeCompression.forward_query_local_positive`, `Monodromy.Counter.Reversible.PrimeCompression.instNeZeroNatModulus`, `Monodromy.Counter.Reversible.PrimeCompression.moduleNode`, `Monodromy.Counter.Reversible.PrimeCompression.moduleRegister`, `Monodromy.Counter.Reversible.PrimeCompression.modulus`, `Monodromy.Counter.Reversible.PrimeCompression.rawEdges`, `Monodromy.Counter.Reversible.PrimeCompression.rawSize`, `Monodromy.Counter.Reversible.PrimeCompression.rawTable`, `Monodromy.Counter.Reversible.PrimeCompression.residue_zero_flag`, `Monodromy.Counter.Reversible.PrimeCompression.restoreInput`, `Monodromy.Counter.Reversible.PrimeCompression.restoreOfTest`, `Monodromy.Counter.Reversible.PrimeCompression.restoreOutput`, `Monodromy.Counter.Reversible.PrimeCompression.restoreRegister_of_test`, `Monodromy.Counter.Reversible.PrimeCompression.restore_connected`, `Monodromy.Counter.Reversible.PrimeCompression.restore_internal_reaches`, `Monodromy.Counter.Reversible.PrimeCompression.restore_pack_local_positive`, `Monodromy.Counter.Reversible.PrimeCompression.reversed`, `Monodromy.Counter.Reversible.PrimeCompression.siteOfEdge`, `Monodromy.Counter.Reversible.PrimeCompression.size`, `Monodromy.Counter.Reversible.PrimeCompression.sourceEdge`, `Monodromy.Counter.Reversible.PrimeCompression.sourceForm_of_test`, `Monodromy.Counter.Reversible.PrimeCompression.sourceInput`, `Monodromy.Counter.Reversible.PrimeCompression.sourceInputPosition`, `Monodromy.Counter.Reversible.PrimeCompression.sourceRegister_of_test`, `Monodromy.Counter.Reversible.PrimeCompression.source_departure`, `Monodromy.Counter.Reversible.PrimeCompression.table`, `Monodromy.Counter.Reversible.PrimeCompression.test_connected`, `Monodromy.Counter.Reversible.PrimeCompression.wiring`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.entry`, `Monodromy.Counter.Reversible.Radix.finish`, `Monodromy.Counter.Reversible.Radix.point`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.Counter.Reversible.step`, `Monodromy.PrimeCode.Basis`, `Monodromy.PrimeCode.Basis.encode`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Reversible.PrimeCompression.test_firstReturn at L8091-L8155 [UTF-8 420569:424743].

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
open Monodromy.Counter.Reversible.PrimeCompression
variable {n q e : ℕ}

theorem Monodromy.Counter.Reversible.PrimeCompression.test_firstReturn (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (before : Counter.Configuration n q) (edge : Fin e) (register : Fin n) (flag : Bool)
    (at_source : (source edge).source = before.pc)
    (test : (source edge).action = .test register flag)
    (enabled : (source edge).action.enabled (fun index => (before.counters index : ℤ))) :
    FirstReturn basis source deterministic compatible
      (encode basis source deterministic compatible before)
      (encode basis source deterministic compatible ⟨(source edge).target, before.counters⟩) := by sorry
