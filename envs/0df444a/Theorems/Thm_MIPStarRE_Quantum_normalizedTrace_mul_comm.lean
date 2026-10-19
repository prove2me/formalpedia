-- Prove2me | Theorems.Thm_MIPStarRE_Quantum_normalizedTrace_mul_comm
-- name    : MIPStarRE.Quantum.normalizedTrace_mul_comm
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:18:05.376859+00:00
-- url     : https://prove2.me/theorems/71153604-c090-456c-93f5-e58167a5c0b4
-- title:
--   The normalized trace is invariant under swapping two multiplicative factors
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteMatrix.NormalizedTrace` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Normalized trace, projectors, and spectral truncation. This module contains the normalized trace `τ`, the squared `τ`-norm, the paper-facing orthogonal-projection name, and the spectral-truncation witness used in the low individual degree test formalization.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   The normalized trace is invariant under swapping two multiplicative factors.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPStarRE
--   open MIPStarRE.Quantum
--   open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
--   open WithLp
--   variable {d : Type*} [Fintype d]
--
--   theorem MIPStarRE.Quantum.normalizedTrace_mul_comm (A B : Op d) :
--       normalizedTrace (A * B) = normalizedTrace (B * A)
--   ```
--
--   **Formalization Note** `MIPStarRE.Quantum.normalizedTrace_mul_comm` is declared in `MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteMatrix/NormalizedTrace.lean`, lines 63–67. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteMatrix/NormalizedTrace.lean#L63-L67

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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace

open MIPStarRE
open MIPStarRE.Quantum
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp
set_option backward.isDefEq.respectTransparency false
variable {d : Type*} [Fintype d]

theorem MIPStarRE.Quantum.normalizedTrace_mul_comm (A B : Op d) :
    normalizedTrace (A * B) = normalizedTrace (B * A) := by sorry
