-- Prove2me | Theorems.Thm_MIPStarRE_LDT_Preliminaries_schwartzZippel_individualDegree
-- name    : MIPStarRE.LDT.Preliminaries.schwartzZippel_individualDegree
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:15:51.272982+00:00
-- url     : https://prove2.me/theorems/2a6b5ddb-c47e-46e1-b8d9-d6acb9a76311
-- title:
--   Schwartz-Zippel for the paper's low-individual-degree class \polyfunc{m}{q}{d}
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.Polynomials` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Polynomial preliminaries. Packages the paper's low-individual-degree polynomial class together with Schwartz-Zippel bounds as thin wrappers around Mathlib's existing multivariate polynomial theorems.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   Schwartz-Zippel for the paper's low-individual-degree class
--   `\polyfunc{m}{q}{d}`.
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
--   theorem MIPStarRE.LDT.Preliminaries.schwartzZippel_individualDegree {m d : ℕ} {K : Type*} [Field K] [Fintype K]
--       [DecidableEq K] (g h : polyFunc m K d) (hneq : g ≠ h) :
--       polynomialAgreementProbability m K g.1 h.1 ≤ ((m * d : ℕ) : ℚ≥0) / Fintype.card K
--   ```
--
--   **Formalization Note** `MIPStarRE.LDT.Preliminaries.schwartzZippel_individualDegree` is declared in `MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Polynomials.lean`, lines 116–131. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Polynomials.lean#L116-L131

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

theorem MIPStarRE.LDT.Preliminaries.schwartzZippel_individualDegree {m d : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (g h : polyFunc m K d) (hneq : g ≠ h) :
    polynomialAgreementProbability m K g.1 h.1 ≤ ((m * d : ℕ) : ℚ≥0) / Fintype.card K := by sorry
