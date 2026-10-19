-- Prove2me | Theorems.Thm_MIPStarRE_LDT_Preliminaries_totalDegree_le_mul_of_degreeOf_le
-- name    : MIPStarRE.LDT.Preliminaries.totalDegree_le_mul_of_degreeOf_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:15:59.439988+00:00
-- url     : https://prove2.me/theorems/7d5a033f-ccda-44d7-bb72-8d9878a76ec1
-- title:
--   If every individual degree of p is at most d, then the total degree of p is at most m * d
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.Polynomials` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Polynomial preliminaries. Packages the paper's low-individual-degree polynomial class together with Schwartz-Zippel bounds as thin wrappers around Mathlib's existing multivariate polynomial theorems.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   If every individual degree of `p` is at most `d`, then the total degree of
--   `p` is at most `m * d`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPStarRE
--   open MIPStarRE.LDT
--   open MIPStarRE.LDT.Preliminaries
--   open Finset Fintype
--   open scoped BigOperators
--   open MvPolynomial
--
--   theorem MIPStarRE.LDT.Preliminaries.totalDegree_le_mul_of_degreeOf_le {m d : ℕ} {K : Type*} [CommSemiring K]
--       {p : MvPolynomial (Fin m) K} (hdeg : ∀ i, p.degreeOf i ≤ d) :
--       p.totalDegree ≤ m * d
--   ```
--
--   **Formalization Note** `MIPStarRE.LDT.Preliminaries.totalDegree_le_mul_of_degreeOf_le` is declared in `MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Polynomials.lean`, lines 69–87. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Polynomials.lean#L69-L87

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials

open MIPStarRE
open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open Finset Fintype
open scoped BigOperators
open MvPolynomial
set_option backward.isDefEq.respectTransparency false

theorem MIPStarRE.LDT.Preliminaries.totalDegree_le_mul_of_degreeOf_le {m d : ℕ} {K : Type*} [CommSemiring K]
    {p : MvPolynomial (Fin m) K} (hdeg : ∀ i, p.degreeOf i ≤ d) :
    p.totalDegree ≤ m * d := by sorry
