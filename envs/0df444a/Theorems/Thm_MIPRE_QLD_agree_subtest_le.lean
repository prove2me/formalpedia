-- Prove2me | Theorems.Thm_MIPRE_QLD_agree_subtest_le
-- name    : MIPRE.QLD.agree_subtest_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:07:26.464781+00:00
-- url     : https://prove2.me/theorems/5e7f4d63-fe97-450e-a900-960e7c199e95
-- title:
--   The master estimate for the Pauli basis test. A subtest that accepts only when two post-processings of the answers agree gives, at error 172 ε, cross-party closeness of the…
-- statement:
--   A statement of the module `MIPRE.Background.QLD.Win` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). What winning the Pauli basis test implies. Blueprint `lem:qld-win`, the paper's `lem:qld-win-implications` (`qld-commutation.tex`). A strategy succeeding with probability `1 - ε` satisfies one cross-party consistency relation per subtest, each at error `O(ε)` --- and the blueprint's proof is exactly one sentence: "each item is the definition of the value of the corresponding subtest, divided by the probability that the subtest is selected". This file makes that sentence mechanical, in two steps.
--
--   **The master estimate for the Pauli basis test.** A subtest that accepts only when two
--   post-processings of the answers agree gives, at error `172 ε`, cross-party closeness of the
--   coarse-grained measurements --- averaged over the verifier's content, which is the "on average
--   over ..." of every item of `lem:qld-win`.
--
--   `S` is the set of contents on which the rule fires: everything for the ungated rules, the
--   commuting or the anticommuting tuples for the four rules gated on `γ`. The weight is `1/#Content`
--   throughout, so for a gated rule this is the *unconditional* average with the gate's indicator
--   inside; the paper's conditional form is this divided by the gate's probability, which is where
--   `fact:omega-anticomm-prob` and the hypothesis `6md ≤ q` enter.
--
--   The `172` is `2 · 86`: the factor `2` of `xSqNorm_sum_le_condFail` and the selection probability
--   `1/86` of `subtest_le`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.QLD
--   open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
--
--   theorem MIPRE.QLD.agree_subtest_le {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
--       {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
--       (hψ : star ψ ⬝ᵥ ψ = 1) {ε : ℝ}
--       (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) {t u : Ty} (htu : adj t u = true)
--       {C : Type*} [Fintype C] [DecidableEq C] (S : Finset (Content F m))
--       (f g : Content F m → Answer F m d → C)
--       (hD : ∀ c ∈ S, ∀ a b, (qldGame hm).D (c.question hm t) (c.question hm u) a b = true →
--         f c a = g c b) :
--       ∑ c ∈ S, (Fintype.card (Content F m) : ℝ)⁻¹ *
--           ∑ o : C, xSqNorm ψ ((((MA (c.question hm t)).map (f c)).mats o).val)
--             ((((MB (c.question hm u)).map (g c)).mats o).val)
--         ≤ 172 * ε
--   ```
--
--   **Formalization Note** `MIPRE.QLD.agree_subtest_le` is declared in `MIPRE/Background/QLD/Win.lean`, lines 137–183. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/Win.lean#L137-L183; blueprint lem:qld-win

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Background_QLD_Win

open MIPRE
open MIPRE.QLD
open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem MIPRE.QLD.agree_subtest_le {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
    {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
    (hψ : star ψ ⬝ᵥ ψ = 1) {ε : ℝ}
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) {t u : Ty} (htu : adj t u = true)
    {C : Type*} [Fintype C] [DecidableEq C] (S : Finset (Content F m))
    (f g : Content F m → Answer F m d → C)
    (hD : ∀ c ∈ S, ∀ a b, (qldGame hm).D (c.question hm t) (c.question hm u) a b = true →
      f c a = g c b) :
    ∑ c ∈ S, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : C, xSqNorm ψ ((((MA (c.question hm t)).map (f c)).mats o).val)
          ((((MB (c.question hm u)).map (g c)).mats o).val)
      ≤ 172 * ε := by sorry
