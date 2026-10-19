-- Prove2me | Theorems.Thm_MIPRE_SAT_Circuit_DescribesDecider_of_pad
-- name    : MIPRE.SAT.Circuit.DescribesDecider.of_pad
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:27:16.298643+00:00
-- url     : https://prove2.me/theorems/9e34fb7d-1abe-415f-80e5-52ed315eabce
-- title:
--   A circuit implementing the padded clause set still describes the same decider, including the entire answer tapes and their blank tails
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.Padding` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Padding decoupled descriptions. The semantic content of `prop:exciting-padding-prop` in `answer_reduction.tex`. The original clauses are embedded in the larger five blocks. Additional clauses force both answer tails to be blank tapes; the three auxiliary tails are free. In particular, the conclusion preserves `Circuit.DescribesDecider`, which specifies every answer bit, rather than merely preserving the accepted answer prefixes. The circuit construction and its running time are separate obligations.
--
--   A circuit implementing the padded clause set still describes the same decider,
--   including the entire answer tapes and their blank tails.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.Circuit
--
--   theorem MIPRE.SAT.Circuit.DescribesDecider.of_pad {C C' : Circuit} {ℓ r ℓ' r' : ℕ}
--       {D : Decider} {n T : ℕ} {x y : Cost.BitStr}
--       (hC : C.DescribesDecider ℓ r D n x y T) (hℓ : ℓ ≤ ℓ') (hr : r ≤ r')
--       (hT : 2 * T ≤ 2 ^ ℓ)
--       (hpad : C'.formula5 ℓ' r' = Cnf5.pad hℓ hr (C.formula5 ℓ r)) :
--       C'.DescribesDecider ℓ' r' D n x y T
--   ```
--
--   **Formalization Note** `MIPRE.SAT.Circuit.DescribesDecider.of_pad` is declared in `MIPRE/Foundations/SAT/Padding.lean`, lines 116–151. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Padding.lean#L116-L151; blueprint lem:pcp-padding-semantics

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Definitions.Def_MIPRE_Foundations_SAT_Padding

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Circuit

theorem MIPRE.SAT.Circuit.DescribesDecider.of_pad {C C' : Circuit} {ℓ r ℓ' r' : ℕ}
    {D : Decider} {n T : ℕ} {x y : Cost.BitStr}
    (hC : C.DescribesDecider ℓ r D n x y T) (hℓ : ℓ ≤ ℓ') (hr : r ≤ r')
    (hT : 2 * T ≤ 2 ^ ℓ)
    (hpad : C'.formula5 ℓ' r' = Cnf5.pad hℓ hr (C.formula5 ℓ r)) :
    C'.DescribesDecider ℓ' r' D n x y T := by sorry
