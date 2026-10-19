-- Prove2me | Theorems.Thm_MIPRE_SAT_viewFormat_rawView
-- name    : MIPRE.SAT.viewFormat_rawView
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:27:28.468758+00:00
-- url     : https://prove2.me/theorems/8549841e-a997-4160-9abe-bb4b49420241
-- title:
--   Lemma viewFormat_rawView of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.Pcp` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The bespoke PCP for deciders: the statement. `MIPRE.SAT.PcpDecider` is blueprint `thm:pcp-decider` — the paper's theorem of the same name in `answer_reduction.tex` — the classical half of answer reduction: a verifier that, given a decider specification and a *PCP view* (a point `z ∈ 𝔽_q^{m'}` and a claimed evaluation of the proof at `z`), accepts an honest low-degree proof with probability `1` and forces any low-degree proof accepted with probability more than `1/2` to encode answers the decider accepts. It consumes `lem:decoupled-5sat` — the decoupled 5SAT description of the decider is what…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.Cost MIPRE.LowDegree MvPolynomial
--
--   theorem MIPRE.SAT.viewFormat_rawView {P : PcpParams} {k : ℕ} (E : BinField k) (hk : P.k = k)
--       (pf : PcpProof P E.carrier) (z : Fin P.m' → E.carrier) :
--       ViewFormat P (pf.rawView E z).1 (pf.rawView E z).2
--   ```
--
--   **Formalization Note** `MIPRE.SAT.viewFormat_rawView` is declared in `MIPRE/Foundations/SAT/Pcp.lean`, lines 196–205. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Pcp.lean#L196-L205; blueprint lem:pcp-format

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
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

open MIPRE
open MIPRE.SAT
open MIPRE.Cost MIPRE.LowDegree MvPolynomial
attribute [instance] MIPRE.SAT.BinField.instField MIPRE.SAT.BinField.instFintype MIPRE.SAT.BinField.instDecidableEq

theorem MIPRE.SAT.viewFormat_rawView {P : PcpParams} {k : ℕ} (E : BinField k) (hk : P.k = k)
    (pf : PcpProof P E.carrier) (z : Fin P.m' → E.carrier) :
    ViewFormat P (pf.rawView E z).1 (pf.rawView E z).2 := by sorry
