-- Prove2me | Theorems.Thm_MIPRE_SAT_PcpParams_formula5_sat_of_majority
-- name    : MIPRE.SAT.PcpParams.formula5_sat_of_majority
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:14:29.618575+00:00
-- url     : https://prove2.me/theorems/e6e7ad42-dd12-42a1-879e-affd56704249
-- title:
--   Majority acceptance supplies an actual satisfying five-tuple for the succinctly described clause set, including every Boolean clause witness
-- statement:
--   A statement of the module `MIPRE.TM.CookLevin.PcpCircuit` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # The circuit polynomial in the PCP clause coordinates
--
--   Majority acceptance supplies an actual satisfying five-tuple for the
--   succinctly described clause set, including every Boolean clause witness.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.PcpParams
--   open MIPRE.LowDegree MvPolynomial
--   variable {F : Type*} [Field F] [CharP F 2]
--
--   theorem MIPRE.SAT.PcpParams.formula5_sat_of_majority [Fintype F] [DecidableEq F]
--       (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
--       (hI : C.inputs = 5 * P.m + 5) (h : C.inputs + C.size = P.m')
--       (pf : PcpProof P F) (hq : 82 * P.m' ≤ Fintype.card F)
--       (S : Finset (Fin P.m' → F))
--       (hS : ∀ z ∈ S, PcpAlgebra.TypedAccepts (P.circuitArith C h) z (pf.ev z))
--       (hmajority : Fintype.card F ^ P.m' < 2 * S.card) :
--       (C.formula5 P.m P.m).Sat (decodedAssignment pf 0) (decodedAssignment pf 1)
--         (decodedAssignment pf 2) (decodedAssignment pf 3) (decodedAssignment pf 4)
--   ```
--
--   **Formalization Note** `MIPRE.SAT.PcpParams.formula5_sat_of_majority` is declared in `MIPRE/TM/CookLevin/PcpCircuit.lean`, lines 140–162. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/PcpCircuit.lean#L140-L162; blueprint lem:pcp-circuit-semantics

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Computability.Language
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
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
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteVariables
import Definitions.Def_MIPRE_Foundations_SAT_FiniteCircuitArithmetization
import Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis
import Definitions.Def_MIPRE_Foundations_SAT_PcpAlgebra
import Definitions.Def_MIPRE_Foundations_SAT_PcpBlocks
import Definitions.Def_MIPRE_TM_CookLevin_PcpClauses
import Definitions.Def_MIPRE_TM_CookLevin_PcpCircuit

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.PcpParams
open MIPRE.LowDegree MvPolynomial
variable {F : Type*} [Field F] [CharP F 2]

theorem MIPRE.SAT.PcpParams.formula5_sat_of_majority [Fintype F] [DecidableEq F]
    (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (hI : C.inputs = 5 * P.m + 5) (h : C.inputs + C.size = P.m')
    (pf : PcpProof P F) (hq : 82 * P.m' ≤ Fintype.card F)
    (S : Finset (Fin P.m' → F))
    (hS : ∀ z ∈ S, PcpAlgebra.TypedAccepts (P.circuitArith C h) z (pf.ev z))
    (hmajority : Fintype.card F ^ P.m' < 2 * S.card) :
    (C.formula5 P.m P.m).Sat (decodedAssignment pf 0) (decodedAssignment pf 1)
      (decodedAssignment pf 2) (decodedAssignment pf 3) (decodedAssignment pf 4) := by sorry
