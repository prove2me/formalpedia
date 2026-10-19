-- Prove2me | Theorems.Thm_MIPRE_ancillaEmbed_isometry
-- name    : MIPRE.ancillaEmbed_isometry
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:21:36.726247+00:00
-- url     : https://prove2.me/theorems/e9d4f741-eca6-4e61-a441-735b74b06814
-- title:
--   Lemma ancillaEmbed_isometry of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.Dilation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Naimark dilation against a fixed state. A POVM is the compression of a projective measurement on a larger space. What the applications need is more than that: a whole *question-indexed family* of POVMs must be the compression of a family of projective measurements by **one** question-independent isometry, because the state the expectations are taken against is shared and must not depend on the question. `exists_projective_dilation` is that statement, and the unitary extension (`exists_unitary_extending`) is the step that buys it. This file was extracted from…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Matrix
--   open scoped ComplexOrder Kronecker MatrixOrder
--
--   theorem MIPRE.ancillaEmbed_isometry {d A : Type*} [Fintype d] [DecidableEq d]
--       [Fintype A] [DecidableEq A] (a₀ : A) :
--       (ancillaEmbed d a₀)ᴴ * ancillaEmbed d a₀ = (1 : Matrix d d ℂ)
--   ```
--
--   **Formalization Note** `MIPRE.ancillaEmbed_isometry` is declared in `MIPRE/Foundations/Dilation.lean`, lines 123–134. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Dilation.lean#L123-L134; blueprint lem:naimark-dilation

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_Dilation

open MIPRE
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

theorem MIPRE.ancillaEmbed_isometry {d A : Type*} [Fintype d] [DecidableEq d]
    [Fintype A] [DecidableEq A] (a₀ : A) :
    (ancillaEmbed d a₀)ᴴ * ancillaEmbed d a₀ = (1 : Matrix d d ℂ) := by sorry
