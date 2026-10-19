-- Prove2me | Theorems.Thm_MIPRE_LIDT_Simul_sum_agreeX_le
-- name    : MIPRE.LIDT.Simul.sum_agreeX_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:03:42.391776+00:00
-- url     : https://prove2.me/theorems/4465c6f5-5855-40bf-9f3d-9c38a5db82a7
-- title:
--   The weighted bound. For nonnegative weights β y b g whose sum over the answer b does not depend on y and totals one over the outcomes, the average agreement of the…
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Extraction` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Extracting exactly linear combined codewords. Blueprint `lem:lidt-ldc-extraction`, the paper's Step 4 of the proof of `lem:ld-soundness` for general `ldc` (`ldt.tex`, Claims 4 and 5 and the measurements `H`, `G`). The simultaneous test with `r` codewords is reduced to the single-codeword test in `K + m` variables by *combining*: a point `(x, y) ∈ F^K × F^m` is answered by `∑_{j < r} x_j b_j`, where `b ∈ F^r` is the original point answer at `y`. The single-codeword theorem then returns a measurement `R` of polynomials `g` in the `K + m` variables, consistent with the combined point answers.…
--
--   **The weighted bound.** For nonnegative weights `β y b g` whose sum over the answer `b` does
--   not depend on `y` and totals one over the outcomes, the average agreement of the combined answer
--   exceeds the average agreement of the extracted tuple by at most `(K + m) d / q`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--   open MIPRE.LIDT.Simul
--   open Finset MIPRE MIPRE.LIDT
--   open scoped Kronecker
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
--
--   theorem MIPRE.LIDT.Simul.sum_agreeX_le (hd : 1 ≤ d) (hr : r ≤ K)
--       (β : Point F m → (Fin r → F) → LowIndDegPoly (F := F) (m := K + m) (d := d) → ℝ)
--       (hβ0 : ∀ y b g, 0 ≤ β y b g) (w : LowIndDegPoly (F := F) (m := K + m) (d := d) → ℝ)
--       (hw : ∀ y g, ∑ b, β y b g = w g) (hw1 : ∑ g, w g = 1) :
--       ∑ y : Point F m, uniform (Point F m) y * ∑ b, ∑ g, β y b g * agreeX hd g y b
--         ≤ ∑ y : Point F m, uniform (Point F m) y *
--             ∑ b, ∑ g, β y b g * (if extEval hd hr g y = b then 1 else 0)
--           + (K + m) * d / Fintype.card F
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.Simul.sum_agreeX_le` is declared in `MIPRE/Background/LIDT/Extraction.lean`, lines 337–402. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Extraction.lean#L337-L402; blueprint lem:lidt-ldc-extraction

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
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Definitions.Def_MIPRE_Background_LIDT_Extraction

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.Simul
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}

theorem MIPRE.LIDT.Simul.sum_agreeX_le (hd : 1 ≤ d) (hr : r ≤ K)
    (β : Point F m → (Fin r → F) → LowIndDegPoly (F := F) (m := K + m) (d := d) → ℝ)
    (hβ0 : ∀ y b g, 0 ≤ β y b g) (w : LowIndDegPoly (F := F) (m := K + m) (d := d) → ℝ)
    (hw : ∀ y g, ∑ b, β y b g = w g) (hw1 : ∑ g, w g = 1) :
    ∑ y : Point F m, uniform (Point F m) y * ∑ b, ∑ g, β y b g * agreeX hd g y b
      ≤ ∑ y : Point F m, uniform (Point F m) y *
          ∑ b, ∑ g, β y b g * (if extEval hd hr g y = b then 1 else 0)
        + (K + m) * d / Fintype.card F := by sorry
