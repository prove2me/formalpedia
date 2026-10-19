-- Prove2me | Theorems.Thm_MIPRE_LowDegree_eq_of_majority_agree
-- name    : MIPRE.LowDegree.eq_of_majority_agree
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:24:28.672099+00:00
-- url     : https://prove2.me/theorems/d335071a-4567-4487-ac04-3bb24d33e77a
-- title:
--   The majority test used by the classical PCP. If the field has at least 2 * m * d elements, agreement at more than half the points forces polynomial equality
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.SchwartzZippel` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The Schwartz–Zippel lemma, in the form the low-degree machinery uses. Blueprint `lem:schwartz-zippel`: two *unequal* polynomials `f, g : 𝔽_q^m → 𝔽_q` of total degree at most `d` agree at a uniformly random point with probability at most `d / q`. Mathlib proves the lemma for a single nonzero polynomial and a product of arbitrary finite subsets (`MvPolynomial.schwartz_zippel_totalDegree`, `schwartz_zippel_sum_degreeOf`). Everything here is the specialization the paper and the blueprint actually quote: * the subsets are all of `F`, so the denominator is `q ^ m` rather than `∏ #(S i)`; * the…
--
--   **The majority test used by the classical PCP.** If the field has at least
--   `2 * m * d` elements, agreement at more than half the points forces polynomial equality.
--   The strict acceptance threshold is essential when the field-size bound is an equality.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open Finset MvPolynomial
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
--
--   theorem MIPRE.LowDegree.eq_of_majority_agree {f g : MvPolynomial (Fin m) F} {d : ℕ}
--       (hf : ∀ i, f.degreeOf i ≤ d) (hg : ∀ i, g.degreeOf i ≤ d)
--       (hsize : 2 * (m * d) ≤ Fintype.card F)
--       (hmajority : Fintype.card F ^ m < 2 * (agree f g).card) : f = g
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.eq_of_majority_agree` is declared in `MIPRE/Foundations/LowDegree/SchwartzZippel.lean`, lines 108–127. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/SchwartzZippel.lean#L108-L127; blueprint lem:pcp-algebra-tests

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel

open MIPRE
open MIPRE.LowDegree
open Finset MvPolynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

theorem MIPRE.LowDegree.eq_of_majority_agree {f g : MvPolynomial (Fin m) F} {d : ℕ}
    (hf : ∀ i, f.degreeOf i ≤ d) (hg : ∀ i, g.degreeOf i ≤ d)
    (hsize : 2 * (m * d) ≤ Fintype.card F)
    (hmajority : Fintype.card F ^ m < 2 * (agree f g).card) : f = g := by sorry
