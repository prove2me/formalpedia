-- Prove2me | Theorems.Thm_MIPRE_SAT_PcpAlgebra_exists_proof_of_satisfying_assignment
-- name    : MIPRE.SAT.PcpAlgebra.exists_proof_of_satisfying_assignment
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:27:27.130983+00:00
-- url     : https://prove2.me/theorems/36f76fae-725b-41e3-a4ff-a2570e05e11c
-- title:
--   The honest low-degree PCP, including its degree-seven certificates and its five prescribed answer polynomials, exists for every satisfying Boolean assignment
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.PcpBlocks` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The five disjoint answer blocks of the classical PCP. The answer polynomials have `m` variables; the formula and certificates have `5*m + 5 + s` variables. This file transports the former into the latter without losing the individual-degree bound. In particular, the honest constraint has degree at most seven, rather than the soundness proof's coarse bound of 41.
--
--   The honest low-degree PCP, including its degree-seven certificates and its
--   five prescribed answer polynomials, exists for every satisfying Boolean assignment.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.PcpAlgebra
--   open Finset MvPolynomial MIPRE.LowDegree
--   variable {P : PcpParams} {F : Type*} [Field F]
--
--   theorem MIPRE.SAT.PcpAlgebra.exists_proof_of_satisfying_assignment
--       (φ : MvPolynomial (Fin P.m') F) (hφdeg : ∀ j, φ.degreeOf j ≤ 6)
--       (hφbool : ∀ y : Fin P.m' → Bool, eval (pt y) φ = 0 ∨ eval (pt y) φ = 1)
--       (a : Fin 5 → (Fin P.m → Bool) → Bool)
--       (hsat : ∀ y : Fin P.m' → Bool, eval (pt y) φ = 1 →
--         ∃ i : Fin 5, a i (P.block i y) = y (P.signIndex i)) :
--       ∃ pf : PcpProof P F,
--         (∀ i, pf.g i = ldEnc (fun x => ofBool (a i x))) ∧
--         ∀ z, TypedAccepts φ z (pf.ev z)
--   ```
--
--   **Formalization Note** `MIPRE.SAT.PcpAlgebra.exists_proof_of_satisfying_assignment` is declared in `MIPRE/Foundations/SAT/PcpBlocks.lean`, lines 174–209. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/PcpBlocks.lean#L174-L209; blueprint lem:pcp-proof-algebra

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis
import Definitions.Def_MIPRE_Foundations_SAT_PcpAlgebra
import Definitions.Def_MIPRE_Foundations_SAT_PcpBlocks

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.PcpAlgebra
open Finset MvPolynomial MIPRE.LowDegree
variable {P : PcpParams} {F : Type*} [Field F]

theorem MIPRE.SAT.PcpAlgebra.exists_proof_of_satisfying_assignment
    (φ : MvPolynomial (Fin P.m') F) (hφdeg : ∀ j, φ.degreeOf j ≤ 6)
    (hφbool : ∀ y : Fin P.m' → Bool, eval (pt y) φ = 0 ∨ eval (pt y) φ = 1)
    (a : Fin 5 → (Fin P.m → Bool) → Bool)
    (hsat : ∀ y : Fin P.m' → Bool, eval (pt y) φ = 1 →
      ∃ i : Fin 5, a i (P.block i y) = y (P.signIndex i)) :
    ∃ pf : PcpProof P F,
      (∀ i, pf.g i = ldEnc (fun x => ofBool (a i x))) ∧
      ∀ z, TypedAccepts φ z (pf.ev z) := by sorry
