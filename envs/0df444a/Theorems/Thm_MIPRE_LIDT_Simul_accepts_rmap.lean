-- Prove2me | Theorems.Thm_MIPRE_LIDT_Simul_accepts_rmap
-- name    : MIPRE.LIDT.Simul.accepts_rmap
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:11:07.758073+00:00
-- url     : https://prove2.me/theorems/00a3b7a9-6830-4573-acdc-d706cab3461a
-- title:
--   Acceptance transfers from the mapped original sample to the combined sample
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Padding` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The padded game adapter. Blueprint `lem:lidt-ldc-adapter`, the paper's Steps 1--2 and Claims 1--3 of the general-`ldc` proof of `lem:ld-soundness` (`ldt.tex`). A strategy for the seeded test with `r` codewords in `m` variables is played as a strategy for the seeded test with one codeword in `K + m` variables: a combined point `(x, y)` is answered by `∑_{j<r} x_j b_j` from the original point answer `b` at `y`, and a combined line by the matching polynomial built from the original line answer.
--
--   **Acceptance transfers** from the mapped original sample to the combined sample.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--   open MIPRE.LIDT.Simul
--   open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
--
--   theorem MIPRE.LIDT.Simul.accepts_rmap (hd : 1 ≤ d) (hK : 1 ≤ K) (σ : Fin (Fintype.card F / m))
--       (sm : CL.Sample F (K + m)) {a b : CL.Answer F m d r}
--       (h : CL.accepts hm (qmap hm hM σ (sm.question hM sm.tyA))
--         (qmap hm hM σ (sm.question hM sm.tyB)) a b = true) :
--       CL.accepts hM (sm.question hM sm.tyA) (sm.question hM sm.tyB)
--         (rmap hM hr (sm.question hM sm.tyA) a) (rmap hM hr (sm.question hM sm.tyB) b) = true
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.Simul.accepts_rmap` is declared in `MIPRE/Background/LIDT/Padding.lean`, lines 593–621. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Padding.lean#L593-L621; blueprint lem:lidt-ldc-adapter

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Degree
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
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Definitions.Def_MIPRE_Background_LIDT_Extraction
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Padding

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.Simul
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K)

theorem MIPRE.LIDT.Simul.accepts_rmap (hd : 1 ≤ d) (hK : 1 ≤ K) (σ : Fin (Fintype.card F / m))
    (sm : CL.Sample F (K + m)) {a b : CL.Answer F m d r}
    (h : CL.accepts hm (qmap hm hM σ (sm.question hM sm.tyA))
      (qmap hm hM σ (sm.question hM sm.tyB)) a b = true) :
    CL.accepts hM (sm.question hM sm.tyA) (sm.question hM sm.tyB)
      (rmap hM hr (sm.question hM sm.tyA) a) (rmap hM hr (sm.question hM sm.tyB) b) = true := by sorry
