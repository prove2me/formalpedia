-- Prove2me | Theorems.Thm_Monodromy_Counter_Reversible_PrimeCompression_encode_injective
-- name    : Monodromy.Counter.Reversible.PrimeCompression.encode_injective
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:29:41.789303+00:00
-- url     : https://prove2.me/theorems/76a871da-8373-4469-b88b-ec666dc6087c
-- title:
--   Prime compression is injective on complete natural configurations
-- statement:
--   For arbitrary natural n,q,e, choose n distinct primes and an n-integer-counter source table whose distinct edges sharing a source or target carry complementary tests of the same register. Its two-counter compression encoding is injective on all natural-counter configurations: it retains the finite control address at the corresponding compressed boundary, stores the prime product $\prod_{i<n}p_i^{x_i}$ in the first integer counter and zero in the second. No unit-shift hypothesis is required for this injectivity assertion.
--
--   Statement dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.PrimeCompression.encode`, `Monodromy.Counter.Reversible.PrimeCompression.size`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.PrimeCode.Basis`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.PortNetwork.control_unlinked_injective`, `Monodromy.Counter.Reversible.PrimeCompression.boundary`, `Monodromy.Counter.Reversible.PrimeCompression.boundary_injective`, `Monodromy.Counter.Reversible.PrimeCompression.boundary_link_none`, `Monodromy.Counter.Reversible.PrimeCompression.encode`, `Monodromy.Counter.Reversible.PrimeCompression.rawEdges`, `Monodromy.Counter.Reversible.PrimeCompression.rawSize`, `Monodromy.Counter.Reversible.PrimeCompression.rawTable`, `Monodromy.Counter.Reversible.PrimeCompression.size`, `Monodromy.Counter.Reversible.PrimeCompression.wiring`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.PrimeCode.Basis`, `Monodromy.PrimeCode.Basis.encode`, `Monodromy.PrimeCode.Basis.encode_injective`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.PrimeCompression.encode`, `Monodromy.Counter.Reversible.PrimeCompression.size`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.PrimeCode.Basis`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.PortNetwork.control_unlinked_injective`, `Monodromy.Counter.Reversible.PrimeCompression.boundary`, `Monodromy.Counter.Reversible.PrimeCompression.boundary_injective`, `Monodromy.Counter.Reversible.PrimeCompression.boundary_link_none`, `Monodromy.Counter.Reversible.PrimeCompression.encode`, `Monodromy.Counter.Reversible.PrimeCompression.rawEdges`, `Monodromy.Counter.Reversible.PrimeCompression.rawSize`, `Monodromy.Counter.Reversible.PrimeCompression.rawTable`, `Monodromy.Counter.Reversible.PrimeCompression.size`, `Monodromy.Counter.Reversible.PrimeCompression.wiring`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.PrimeCode.Basis`, `Monodromy.PrimeCode.Basis.encode`, `Monodromy.PrimeCode.Basis.encode_injective`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Reversible.PrimeCompression.encode_injective at L7581-L7598 [UTF-8 387916:389057].

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

theorem Monodromy.Counter.Reversible.PrimeCompression.encode_injective (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) :
    Function.Injective (encode basis source deterministic compatible) := by sorry
