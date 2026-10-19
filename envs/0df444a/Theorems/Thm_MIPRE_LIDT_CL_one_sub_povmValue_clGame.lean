-- Prove2me | Theorems.Thm_MIPRE_LIDT_CL_one_sub_povmValue_clGame
-- name    : MIPRE.LIDT.CL.one_sub_povmValue_clGame
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:27:53.076332+00:00
-- url     : https://prove2.me/theorems/937742b9-e9b6-41ed-a03b-a3f548ec0ace
-- title:
--   The failure probability of a POVM strategy in the seeded test is the average over the verifier's samples of the conditional failure at the two questions the sample generates
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Adapter.Value` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The value of a strategy for the seeded test, sample by sample. The seeded test's question distribution is the push-forward of the uniform distribution on `Sample F m` under the two typed question maps. A strategy's failure probability is therefore the average over samples of the conditional failure at the two questions the sample generates (`one_sub_povmValue_clGame`), and that average splits into the nine ordered type pairs (`sum_sample_eq`). The padded strategy of the Pauli basis test is analysed one type pair at a time, which is what these two identities are for. The file also records two…
--
--   **The failure probability of a POVM strategy in the seeded test is the average over the
--   verifier's samples of the conditional failure at the two questions the sample generates.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--   open MIPRE.LIDT.CL
--   open Finset MIPRE
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ}
--   variable [NeZero m] (hm : m ∣ Fintype.card F)
--
--   theorem MIPRE.LIDT.CL.one_sub_povmValue_clGame {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
--       [DecidableEq dB] (ψ : dA × dB → ℂ) (MA : Question F m → POVM (Answer F m d ldc) dA)
--       (MB : Question F m → POVM (Answer F m d ldc) dB) :
--       1 - povmValue (clGame (d := d) (ldc := ldc) hm) ψ MA MB
--         = (Fintype.card (Sample F m) : ℝ)⁻¹ * ∑ sm : Sample F m,
--             condFail (clGame hm) ψ MA MB (sm.question hm sm.tyA) (sm.question hm sm.tyB)
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.CL.one_sub_povmValue_clGame` is declared in `MIPRE/Background/LIDT/Adapter/Value.lean`, lines 134–161. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Adapter/Value.lean#L134-L161; blueprint lem:qld-global-setup

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Value

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.CL
open Finset MIPRE
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ}
variable [NeZero m] (hm : m ∣ Fintype.card F)

theorem MIPRE.LIDT.CL.one_sub_povmValue_clGame {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
    [DecidableEq dB] (ψ : dA × dB → ℂ) (MA : Question F m → POVM (Answer F m d ldc) dA)
    (MB : Question F m → POVM (Answer F m d ldc) dB) :
    1 - povmValue (clGame (d := d) (ldc := ldc) hm) ψ MA MB
      = (Fintype.card (Sample F m) : ℝ)⁻¹ * ∑ sm : Sample F m,
          condFail (clGame hm) ψ MA MB (sm.question hm sm.tyA) (sm.question hm sm.tyB) := by sorry
