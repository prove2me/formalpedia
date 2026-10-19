-- Prove2me | Theorems.Thm_MIPRE_LIDT_CL_Regs_questionOf_eval
-- name    : MIPRE.LIDT.CL.Regs.questionOf_eval
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:11:13.914307+00:00
-- url     : https://prove2.me/theorems/f238ff18-9ae3-448c-ad48-56bc6fd4a118
-- title:
--   The presentation computes the seeded question of the sample the registers carry
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Presentation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded low-degree questions as CL functions, on any registers. The paper's typed CL functions `L_Point`, `L_ALine`, `L_DLine` (`ldt.tex`, `eq:cl-ptf` to `eq:cl-dlnf`) act on three registers of an ambient space: a point register `V_pt ≅ F^n`, a coordinate (seed) register `V_coord ≅ F` and a direction register `V_dir ≅ F^n`. The answer-reduced sampler (`sec:ar-verifier`) uses six copies of them on *overlapping* registers of one ambient space, so the registers are data here: `Regs ι n` places them in the coordinates `ι` of the ambient space by two injections and a coordinate. Every type gets…
--
--   **The presentation computes the seeded question** of the sample the registers carry.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--   open MIPRE.LIDT.CL
--   open MIPRE.LIDT.CL.Regs
--   open Finset MIPRE.CL
--   variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
--   variable {F : Type*} [Field F]
--   variable [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F} (S : Sel F n hn)
--
--   theorem MIPRE.LIDT.CL.Regs.questionOf_eval (t : Ty) (x : ι → F) :
--       R.questionOf S t ((R.pres S t).eval x) = (R.sampleOf S t x).question hn t
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.CL.Regs.questionOf_eval` is declared in `MIPRE/Background/LIDT/Presentation.lean`, lines 320–362. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Presentation.lean#L320-L362; blueprint def:ar-pcp-sampler

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.CL
open MIPRE.LIDT.CL.Regs
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]
variable [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F} (S : Sel F n hn)

theorem MIPRE.LIDT.CL.Regs.questionOf_eval (t : Ty) (x : ι → F) :
    R.questionOf S t ((R.pres S t).eval x) = (R.sampleOf S t x).question hn t := by sorry
