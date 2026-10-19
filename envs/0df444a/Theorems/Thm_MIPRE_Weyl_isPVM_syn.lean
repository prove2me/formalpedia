-- Prove2me | Theorems.Thm_MIPRE_Weyl_isPVM_syn
-- name    : MIPRE.Weyl.isPVM_syn
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:44:40.923181+00:00
-- url     : https://prove2.me/theorems/e17afdac-b9d7-489b-98e0-96196406a1d0
-- title:
--   The syndrome projectors form a projective measurement, indexed by the value of the pairing
-- statement:
--   A statement of the module `MIPRE.Foundations.WeylEPR` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The maximally entangled state of the Weyl system. `|EPR_q⟩^{⊗ n}` on two copies of `(C^q)^{⊗ n}`, normalized, and the one property the Pauli basis test uses it for: **the two parties' Weyl operators act identically on it.** That property is the reason the expansion stage of the appendix works at all. Its expanded state adjoins `|EPR_q⟩^{⊗ M}` to each player, and the sign `(-1)^γ` that the strategy's own observables carry is cancelled against one the *ancilla* observables carry; for that the ancilla halves must be tied together, and `stateVec_epr_wX`/`stateVec_epr_wZ` is the tie.
--
--   **The syndrome projectors form a projective measurement**, indexed by the value of the
--   pairing.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Weyl
--   open Finset Matrix MIPRE
--   open scoped Kronecker
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
--   variable {n : Type*} [Fintype n] [DecidableEq n]
--   variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
--
--   theorem MIPRE.Weyl.isPVM_syn (hw : IsWeylFamily w) (v : n → F) : IsPVM (syn w v)
--   ```
--
--   **Formalization Note** `MIPRE.Weyl.isPVM_syn` is declared in `MIPRE/Foundations/WeylEPR.lean`, lines 187–190. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/WeylEPR.lean#L187-L190; blueprint def:weyl-epr

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
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_WeylEPR

open MIPRE
open MIPRE.Weyl
open Finset Matrix MIPRE
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}

theorem MIPRE.Weyl.isPVM_syn (hw : IsWeylFamily w) (v : n → F) : IsPVM (syn w v) := by sorry
