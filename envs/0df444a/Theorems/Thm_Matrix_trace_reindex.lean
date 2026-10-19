-- Prove2me | Theorems.Thm_Matrix_trace_reindex
-- name    : Matrix.trace_reindex
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:17:47.486976+00:00
-- url     : https://prove2.me/theorems/23838b8b-66db-4828-83c4-3b871a3013ac
-- title:
--   Reindexing rows and columns by the same equivalence preserves matrix trace
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteMatrix.Basic` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Basic finite-dimensional matrix operators. This module contains the elementary trace and matrix-algebra facts used by the finite-dimensional quantum layer. It introduces the local operator abbreviation `Op d = Matrix d d ℂ` and keeps the basic trace bookkeeping independent of the positive-semidefinite order and normalized-trace material.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   Reindexing rows and columns by the same equivalence preserves matrix trace.
--
--   This generic matrix lemma is used when moving between equivalent finite index
--   presentations of the same operator.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open Matrix
--   open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
--   open WithLp
--
--   theorem Matrix.trace_reindex {α β R : Type*} [Fintype α] [Fintype β]
--       [AddCommMonoid R] (e : α ≃ β) (M : Matrix α α R) :
--       Matrix.trace (Matrix.reindex e e M) = Matrix.trace M
--   ```
--
--   **Formalization Note** `Matrix.trace_reindex` is declared in `MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteMatrix/Basic.lean`, lines 67–77. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteMatrix/Basic.lean#L67-L77

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic

open Matrix
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp
set_option backward.isDefEq.respectTransparency false

theorem Matrix.trace_reindex {α β R : Type*} [Fintype α] [Fintype β]
    [AddCommMonoid R] (e : α ≃ β) (M : Matrix α α R) :
    Matrix.trace (Matrix.reindex e e M) = Matrix.trace M := by sorry
