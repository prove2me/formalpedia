-- Prove2me | Theorems.Thm_MIPRE_sum_snorm_sq_chain
-- name    : MIPRE.sum_snorm_sq_chain
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:15:37.637992+00:00
-- url     : https://prove2.me/theorems/163af43d-eb2b-4be0-8f0a-a130c48ec3d7
-- title:
--   The per-seed algebra. C_u ⊗ Q_v - O^𝖠_u O^𝖡_v ⊗ Id splits into three cross-party deviations, each behind a front factor that is a projective measurement and so costs nothing…
-- statement:
--   A statement of the module `MIPRE.Foundations.OracularTensor` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Soundness of oracularization, for bipartite strategies. Item 2 of blueprint `thm:oracularization` (`lem:oracular-soundness-tensor`), at the level of games and for **arbitrary tensor-product strategies**: a strategy of value at least `1 - ε` for `MIPRE.SeededGame.oracular` yields one of value at least `1 - 24√ε` for the input game, and so `val*` of the oracularization above `1 - ε` puts `val*` of the input at least `1 - 24√ε`. `MIPRE/Foundations/OracularSound.lean` proves the same bound for *synchronous* strategies. That is not the statement a verifier-level consumer can use:…
--
--   **The per-seed algebra.** `C_u ⊗ Q_v - O^𝖠_u O^𝖡_v ⊗ Id` splits into three cross-party
--   deviations, each behind a front factor that is a projective measurement and so costs nothing
--   summed over its outcome.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder
--   variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
--
--   theorem MIPRE.sum_snorm_sq_chain (ψ : HA × HB → ℂ) {K : Type*} [Fintype K] [DecidableEq K]
--       (C OA OB : K → Matrix HA HA ℂ) (P Q : K → Matrix HB HB ℂ) (hQ : IsPVM Q) (hOA : IsPVM OA) :
--       ∑ o : K × K,
--           snorm ψ ((aOp (C o.1) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (Q o.2)
--             - aOp (OA o.1 * OB o.2)) ^ 2
--         ≤ 3 * ∑ u, snorm ψ ((aOp (C u) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (P u)) ^ 2
--           + 3 * ∑ u, snorm ψ ((aOp (OA u) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (P u)) ^ 2
--           + 3 * ∑ v, snorm ψ ((aOp (OB v) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (Q v)) ^ 2
--   ```
--
--   **Formalization Note** `MIPRE.sum_snorm_sq_chain` is declared in `MIPRE/Foundations/OracularTensor.lean`, lines 200–257. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/OracularTensor.lean#L200-L257

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_OracularTensor

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

theorem MIPRE.sum_snorm_sq_chain (ψ : HA × HB → ℂ) {K : Type*} [Fintype K] [DecidableEq K]
    (C OA OB : K → Matrix HA HA ℂ) (P Q : K → Matrix HB HB ℂ) (hQ : IsPVM Q) (hOA : IsPVM OA) :
    ∑ o : K × K,
        snorm ψ ((aOp (C o.1) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (Q o.2)
          - aOp (OA o.1 * OB o.2)) ^ 2
      ≤ 3 * ∑ u, snorm ψ ((aOp (C u) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (P u)) ^ 2
        + 3 * ∑ u, snorm ψ ((aOp (OA u) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (P u)) ^ 2
        + 3 * ∑ v, snorm ψ ((aOp (OB v) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (Q v)) ^ 2 := by sorry
