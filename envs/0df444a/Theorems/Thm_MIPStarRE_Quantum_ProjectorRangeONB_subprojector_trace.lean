-- Prove2me | Theorems.Thm_MIPStarRE_Quantum_ProjectorRangeONB_subprojector_trace
-- name    : MIPStarRE.Quantum.ProjectorRangeONB.subprojector_trace
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:18:59.278184+00:00
-- url     : https://prove2.me/theorems/2a131461-e2b9-4fb0-b7ff-670e46e8f79d
-- title:
--   The partial projector's trace is the number of selected vectors
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.MIPStarRE.Quantum.ProjectorONB` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Projector Range Orthonormal Bases. This file packages the finite-dimensional spectral decomposition of an orthogonal projector as an orthonormal basis of its range. It supplies the rank-one decomposition needed by the rank-reduction truncation branch in the low-degree-test formalization.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   The partial projector's trace is the number of selected vectors.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPStarRE
--   open MIPStarRE.Quantum
--   open MIPStarRE.Quantum.ProjectorRangeONB
--   open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.L2Operator
--   variable {ι : Type*} [Fintype ι] [DecidableEq ι]
--   variable {P : Op ι} {hP : IsProj P} (b : ProjectorRangeONB P hP)
--
--   theorem MIPStarRE.Quantum.ProjectorRangeONB.subprojector_trace (S : Finset (Fin P.rank)) :
--       (b.subprojector S).trace = (S.card : ℂ)
--   ```
--
--   **Formalization Note** `MIPStarRE.Quantum.ProjectorRangeONB.subprojector_trace` is declared in `MIPRE/Background/LIDT/MIPStarRE/Quantum/ProjectorONB.lean`, lines 275–290. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/Quantum/ProjectorONB.lean#L275-L290

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
import Mathlib.Analysis.Matrix.Spectrum
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_ProjectorONB

open MIPStarRE
open MIPStarRE.Quantum
open MIPStarRE.Quantum.ProjectorRangeONB
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Op ι} {hP : IsProj P} (b : ProjectorRangeONB P hP)
omit [DecidableEq ι]

theorem MIPStarRE.Quantum.ProjectorRangeONB.subprojector_trace (S : Finset (Fin P.rank)) :
    (b.subprojector S).trace = (S.card : ℂ) := by sorry
