-- Prove2me | Theorems.Thm_OAI_HadwigerCounterexample_corollary_1_2
-- name    : OAI.HadwigerCounterexample.corollary_1_2
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T21:56:20.547681+00:00
-- url     : https://prove2.me/theorems/73ca88e4-49c0-4130-8823-cc1fe242a9aa
-- title:
--   Corollary 1.2 — fractional chromatic counterexamples
-- statement:
--   Corollary 1.2 of the source preprint (p. 3). There are finite nonempty simple graphs $G$ of arbitrarily large order $m$ for which
--   $$h(G)<\frac{26m}{75}+\frac23<\frac m2\le\chi_f(G)\le\chi(G),$$
--   where $h(G)$ is the Hadwiger number, $\chi_f(G)$ the fractional chromatic number, and $\chi(G)$ the chromatic number. Thus Hadwiger's conjecture and its fractional-coloring weakening $\chi_f(G)\le h(G)$ (discussed by Reed and Seymour) are both false.
--
--   The lower bound $\chi_f(G)\ge m/2$ follows by summing the vertex constraints of any fractional coloring and using $\alpha(G)\le2$; the upper bound on $h(G)$ is the matching–minor bound applied to the graphs of Theorem 1.1. The chain is stated for $m\ge5$, where $26m/75+2/3<m/2$.
--
--   **Formalization Note.** Newly transcribed from the paper's Corollary 1.2 (the authors' bundled Lean theorem `exists_counterexamples` records the ordinary-chromatic chain but not the fractional term). Stated over `ℝ`; $\chi_f$ is `fractionalChromaticNumber` and $\chi$ is represented by the finite value `chromaticNumber.toNat`. This item should be compile-checked at submission.
-- source:
--   https://github.com/openai/math/blob/main/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf , p. 3, Corollary 1.2

import Mathlib
import Definitions.Def_HadwigerMatching_Defs
import Definitions.Def_ListHadwiger
import Definitions.Def_HadwigerCounterexample_Fractional

open OAI.HadwigerMatching OAI.LinearListHadwiger OAI.HadwigerCounterexample

namespace OAI.HadwigerCounterexample

theorem corollary_1_2 (M : ℕ) : ∃ m : ℕ, max M 5 ≤ m ∧
    ∃ G : SimpleGraph (Fin m),
      (hadwigerNumber G : ℝ) < 26 * (m : ℝ) / 75 + 2 / 3 ∧
      26 * (m : ℝ) / 75 + 2 / 3 < (m : ℝ) / 2 ∧
      (m : ℝ) / 2 ≤ fractionalChromaticNumber G ∧
      fractionalChromaticNumber G ≤ (G.chromaticNumber.toNat : ℝ) := by sorry

end OAI.HadwigerCounterexample
