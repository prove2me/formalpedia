-- Prove2me | Theorems.Thm_MIPRE_CL_rightPart_ofBits
-- name    : MIPRE.CL.rightPart_ofBits
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:21:07.866889+00:00
-- url     : https://prove2.me/theorems/cbcab0c8-f24a-4cc5-8a09-ac6cdb8323d3
-- title:
--   Lemma rightPart_ofBits of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.ProductSampler` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The product of a typed sampler and a directly answered one: the presentations. The answer-reduced sampler (`sec:ar-verifier`, `ld_compiler.tex`) is the direct sum of the oracularized sampler, whose queries are answered by a program, and the downsized PCP sampler, whose queries a polynomial-time function answers outright. This file is the CL half of that construction, for any two families of presentations on `𝔽₂^a` and `𝔽₂^b`: * `prodCL L P Q` pads both to `L` levels and puts them side by side on `𝔽₂^{a + b}`, the first `a` coordinates for `P`; * its three queries, in bits, are the two halves'…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open Finset MIPRE.Cost
--   variable {a b : ℕ}
--
--   theorem MIPRE.CL.rightPart_ofBits (l : BitStr) :
--       rightPart (ofBits (a + b) l) = ofBits b (l.drop a)
--   ```
--
--   **Formalization Note** `MIPRE.CL.rightPart_ofBits` is declared in `MIPRE/Foundations/CL/ProductSampler.lean`, lines 108–111. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/ProductSampler.lean#L108-L111

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_CL_ProductSampler

open MIPRE
open MIPRE.CL
open Finset MIPRE.Cost
variable {a b : ℕ}

theorem MIPRE.CL.rightPart_ofBits (l : BitStr) :
    rightPart (ofBits (a + b) l) = ofBits b (l.drop a) := by sorry
