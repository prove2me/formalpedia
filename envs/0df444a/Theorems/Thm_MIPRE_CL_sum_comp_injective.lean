-- Prove2me | Theorems.Thm_MIPRE_CL_sum_comp_injective
-- name    : MIPRE.CL.sum_comp_injective
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:11:06.961062+00:00
-- url     : https://prove2.me/theorems/7625e8db-6ad8-4189-900a-c6df287a1708
-- title:
--   Summing over vectors through an injection of coordinates: x ↦ x ∘ e has fibres of size q^{|ι| - |κ|}
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Presentation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded low-degree questions as CL functions, on any registers. The paper's typed CL functions `L_Point`, `L_ALine`, `L_DLine` (`ldt.tex`, `eq:cl-ptf` to `eq:cl-dlnf`) act on three registers of an ambient space: a point register `V_pt ≅ F^n`, a coordinate (seed) register `V_coord ≅ F` and a direction register `V_dir ≅ F^n`. The answer-reduced sampler (`sec:ar-verifier`) uses six copies of them on *overlapping* registers of one ambient space, so the registers are data here: `Regs ι n` places them in the coordinates `ι` of the ambient space by two injections and a coordinate. Every type gets…
--
--   **Summing over vectors through an injection of coordinates**: `x ↦ x ∘ e` has fibres of
--   size `q^{|ι| - |κ|}`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open Finset
--
--   theorem MIPRE.CL.sum_comp_injective {κ ι F M : Type*} [Fintype κ] [DecidableEq κ]
--       [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] [AddCommMonoid M] (e : κ → ι)
--       (he : Function.Injective e) (g : (κ → F) → M) :
--       ∑ x : ι → F, g (x ∘ e)
--         = (Fintype.card F ^ (Fintype.card ι - Fintype.card κ)) • ∑ y : κ → F, g y
--   ```
--
--   **Formalization Note** `MIPRE.CL.sum_comp_injective` is declared in `MIPRE/Background/LIDT/Presentation.lean`, lines 33–70. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Presentation.lean#L33-L70; blueprint def:ar-pcp-sampler

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
open MIPRE.CL
open Finset

theorem MIPRE.CL.sum_comp_injective {κ ι F M : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] [AddCommMonoid M] (e : κ → ι)
    (he : Function.Injective e) (g : (κ → F) → M) :
    ∑ x : ι → F, g (x ∘ e)
      = (Fintype.card F ^ (Fintype.card ι - Fintype.card κ)) • ∑ y : κ → F, g y := by sorry
