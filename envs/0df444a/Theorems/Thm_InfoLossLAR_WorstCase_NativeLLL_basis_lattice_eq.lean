-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_NativeLLL_basis_lattice_eq
-- name    : InfoLossLAR.WorstCase.NativeLLL.basis_lattice_eq
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T04:40:48.531197+00:00
-- url     : https://prove2.me/theorems/f5fa5390-bdea-472b-bdfa-66fc0c19b62b
-- title:
--   The concrete LLL reducer preserves the original column lattice exactly
-- statement:
--   For every square integer matrix B, the column matrix basis B produced by the concrete logarithmic-budget LLL reducer generates exactly the same set of Euclidean lattice vectors as B. The statement is an equality of the original lattice sets and includes singular inputs. The row-basis implementation and the column-basis interface are connected by the explicitly defined transpose conversion; no replacement lattice or approximate membership relation is used.
-- source:
--   Existing checked theorem InfoLossLAR.WorstCase.NativeLLL.basis_lattice_eq in Solutions.RegevBridgeNativeLLLOriginalBasis.lean. The submitted declaration and its supporting proofs are extracted from the checked Lean source using the kernel dependency graph and Lean syntax positions. The vendor mathematics uses the frozen leanprover/hex-lll dependency family; original Apache-2.0 license and copyright notices are retained in the proof sources. This submission adds no new mathematical claim. Existing checked Lean theorem from Solutions.RegevBridgeNativeLLLOriginalBasis, original source lines 44–67. Original proof commands are selected using the official Lean declaration/sketch and syntax oracles, with only declared-name/reference remapping. Recursive self references, when renamed, are recovered from matching original Lean local-fvar identities. The original theorem and all inlined helper types are kernel checked; the complete proof and all its generated declarations use only the standard three axioms. Apache-2.0 notices and source provenance are preserved.

import Definitions.Def_InfoLossLAR_IntegerBasis_Core
import Definitions.Def_InfoLossLAR_WorstCase_LatticeProblems
import Definitions.Def_LARLLL_CurrentData
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Init
import Init.Data.List.Sort.Basic
import Init.Grind.Ring.Field
import Lean
import Mathlib
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Vector.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Order.Hom.Set
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Tactic
import Std
import Std.Data.ExtTreeMap.Lemmas
set_option autoImplicit false
set_option maxRecDepth 8192

theorem _root_.InfoLossLAR.WorstCase.NativeLLL.basis_lattice_eq : ∀ {n : Nat} (B : Matrix.{0, 0, 0} (Fin n) (Fin n) Int),
  @Eq.{1} (Set.{0} (EuclideanSpace.{0, 0} Real (Fin n)))
    (@InfoLossLAR.WorstCase.lattice n (@InfoLossLAR.WorstCase.NativeLLL.basis n B)) (@InfoLossLAR.WorstCase.lattice n B) := by sorry
