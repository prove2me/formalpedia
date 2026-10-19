-- Prove2me | Theorems.Thm_MIPStarRE_LDT_Preliminaries_schwartzZippel_totalDegree
-- name    : MIPStarRE.LDT.Preliminaries.schwartzZippel_totalDegree
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:16:04.506778+00:00
-- url     : https://prove2.me/theorems/a77715d7-a9c1-4ca2-aba4-41e228ed63a1
-- title:
--   If two polynomials on K^m have total degree at most d, then the uniform agreement probability is at most d / |K|
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.Polynomials` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Polynomial preliminaries. Packages the paper's low-individual-degree polynomial class together with Schwartz-Zippel bounds as thin wrappers around Mathlib's existing multivariate polynomial theorems.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   If two polynomials on `K^m` have total degree at most `d`, then the uniform
--   agreement probability is at most `d / |K|`.
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
--   theorem MIPStarRE.LDT.Preliminaries.schwartzZippel_totalDegree {m d : ℕ} {K : Type*} [Field K] [Fintype K]
--       [DecidableEq K] {g h : MvPolynomial (Fin m) K} (hneq : g ≠ h)
--       (hg : g.totalDegree ≤ d) (hh : h.totalDegree ≤ d) :
--       polynomialAgreementProbability m K g h ≤ d / Fintype.card K
--   ```
--
--   **Formalization Note** `MIPStarRE.LDT.Preliminaries.schwartzZippel_totalDegree` is declared in `MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Polynomials.lean`, lines 89–114. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Polynomials.lean#L89-L114

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

theorem MIPStarRE.LDT.Preliminaries.schwartzZippel_totalDegree {m d : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] {g h : MvPolynomial (Fin m) K} (hneq : g ≠ h)
    (hg : g.totalDegree ≤ d) (hh : h.totalDegree ≤ d) :
    polynomialAgreementProbability m K g h ≤ d / Fintype.card K := by sorry
