-- Prove2me | Theorems.Thm_MIPRE_LIDT_Simul_extracted_conclusions
-- name    : MIPRE.LIDT.Simul.extracted_conclusions
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:03:47.743984+00:00
-- url     : https://prove2.me/theorems/f93d670b-93fe-4894-ac34-04c1b4703bfc
-- title:
--   From the single-codeword conclusions to the simultaneous ones (the paper's Step 4)
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Extraction` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Extracting exactly linear combined codewords. Blueprint `lem:lidt-ldc-extraction`, the paper's Step 4 of the proof of `lem:ld-soundness` for general `ldc` (`ldt.tex`, Claims 4 and 5 and the measurements `H`, `G`). The simultaneous test with `r` codewords is reduced to the single-codeword test in `K + m` variables by *combining*: a point `(x, y) ∈ F^K × F^m` is answered by `∑_{j < r} x_j b_j`, where `b ∈ F^r` is the original point answer at `y`. The single-codeword theorem then returns a measurement `R` of polynomials `g` in the `K + m` variables, consistent with the combined point answers.…
--
--   **From the single-codeword conclusions to the simultaneous ones** (the paper's Step 4). If the
--   two players' measurements `RA`, `RB` of polynomials in the `K + m` variables satisfy the three
--   conclusions of the single-codeword theorem against the combined point measurements, with error
--   `δ`, then their extractions satisfy the three conclusions of the simultaneous theorem against the
--   original point measurements, with error `δ + (K + m) d / q` for the two point conclusions and `δ`
--   for the full-tuple one.
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
--   theorem MIPRE.LIDT.Simul.extracted_conclusions (hd : 1 ≤ d) (hr : r ≤ K) {ψ : dA × dB → ℂ}
--       (hψ : star ψ ⬝ᵥ ψ = 1) (A : Point F m → POVM (Fin r → F) dA)
--       (B : Point F m → POVM (Fin r → F) dB)
--       (RA : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := K + m) (d := d))
--         (Matrix dA dA ℂ))
--       (RB : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := K + m) (d := d))
--         (Matrix dB dB ℂ)) {δ : ℝ}
--       (h1 : inconsistency (uniform (Point F (K + m))) ψ (combPOVM hd A) (evalPOVM RB) ≤ δ)
--       (h2 : inconsistency (uniform (Point F (K + m))) ψ (evalPOVM RA) (combPOVM hd B) ≤ δ)
--       (h3 : inconsistency (uniform Unit) ψ (fun _ => RA.toPOVM ()) (fun _ => RB.toPOVM ()) ≤ δ) :
--       inconsistency (uniform (Point F m)) ψ A (evalTuplePOVM (extractPM hd hr RB))
--           ≤ δ + (K + m) * d / Fintype.card F ∧
--         inconsistency (uniform (Point F m)) ψ (evalTuplePOVM (extractPM hd hr RA)) B
--           ≤ δ + (K + m) * d / Fintype.card F ∧
--         inconsistency (uniform Unit) ψ (fun _ => (extractPM hd hr RA).toPOVM ())
--           (fun _ => (extractPM hd hr RB).toPOVM ()) ≤ δ
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.Simul.extracted_conclusions` is declared in `MIPRE/Background/LIDT/Extraction.lean`, lines 716–757. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Extraction.lean#L716-L757; blueprint lem:lidt-ldc-extraction

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
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem MIPRE.LIDT.Simul.extracted_conclusions (hd : 1 ≤ d) (hr : r ≤ K) {ψ : dA × dB → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (A : Point F m → POVM (Fin r → F) dA)
    (B : Point F m → POVM (Fin r → F) dB)
    (RA : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := K + m) (d := d))
      (Matrix dA dA ℂ))
    (RB : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := K + m) (d := d))
      (Matrix dB dB ℂ)) {δ : ℝ}
    (h1 : inconsistency (uniform (Point F (K + m))) ψ (combPOVM hd A) (evalPOVM RB) ≤ δ)
    (h2 : inconsistency (uniform (Point F (K + m))) ψ (evalPOVM RA) (combPOVM hd B) ≤ δ)
    (h3 : inconsistency (uniform Unit) ψ (fun _ => RA.toPOVM ()) (fun _ => RB.toPOVM ()) ≤ δ) :
    inconsistency (uniform (Point F m)) ψ A (evalTuplePOVM (extractPM hd hr RB))
        ≤ δ + (K + m) * d / Fintype.card F ∧
      inconsistency (uniform (Point F m)) ψ (evalTuplePOVM (extractPM hd hr RA)) B
        ≤ δ + (K + m) * d / Fintype.card F ∧
      inconsistency (uniform Unit) ψ (fun _ => (extractPM hd hr RA).toPOVM ())
        (fun _ => (extractPM hd hr RB).toPOVM ()) ≤ δ := by sorry
