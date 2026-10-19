-- Prove2me | Theorems.Thm_MIPRE_LowDegree_prob_agree_le_individualDegree
-- name    : MIPRE.LowDegree.prob_agree_le_individualDegree
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:23:35.622518+00:00
-- url     : https://prove2.me/theorems/a7500106-c9b2-4604-a063-596bf23457dd
-- title:
--   The individual-degree variant: if f ≠ g and both have degree at most d in each of the m variables separately, they agree with probability at most m * d / q
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.SchwartzZippel` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The Schwartz–Zippel lemma, in the form the low-degree machinery uses. Blueprint `lem:schwartz-zippel`: two *unequal* polynomials `f, g : 𝔽_q^m → 𝔽_q` of total degree at most `d` agree at a uniformly random point with probability at most `d / q`. Mathlib proves the lemma for a single nonzero polynomial and a product of arbitrary finite subsets (`MvPolynomial.schwartz_zippel_totalDegree`, `schwartz_zippel_sum_degreeOf`). Everything here is the specialization the paper and the blueprint actually quote: * the subsets are all of `F`, so the denominator is `q ^ m` rather than `∏ #(S i)`; * the…
--
--   The individual-degree variant: if `f ≠ g` and both have degree at most `d` in each of
--   the `m` variables separately, they agree with probability at most `m * d / q`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open Finset MvPolynomial
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
--
--   theorem MIPRE.LowDegree.prob_agree_le_individualDegree {f g : MvPolynomial (Fin m) F} (hfg : f ≠ g) {d : ℕ}
--       (hf : ∀ i, f.degreeOf i ≤ d) (hg : ∀ i, g.degreeOf i ≤ d) :
--       ((agree f g).card : ℝ) / (Fintype.card F : ℝ) ^ m ≤ (m : ℝ) * d / Fintype.card F
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.prob_agree_le_individualDegree` is declared in `MIPRE/Foundations/LowDegree/SchwartzZippel.lean`, lines 83–106. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/SchwartzZippel.lean#L83-L106; blueprint lem:schwartz-zippel

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

theorem MIPRE.LowDegree.prob_agree_le_individualDegree {f g : MvPolynomial (Fin m) F} (hfg : f ≠ g) {d : ℕ}
    (hf : ∀ i, f.degreeOf i ≤ d) (hg : ∀ i, g.degreeOf i ≤ d) :
    ((agree f g).card : ℝ) / (Fintype.card F : ℝ) ^ m ≤ (m : ℝ) * d / Fintype.card F := by sorry
