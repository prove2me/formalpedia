-- Prove2me | Theorems.Thm_LearnStability_ERMLOO_lemma15
-- name    : LearnStability.ERMLOO.lemma15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T18:32:13.938985+00:00
-- url     : https://prove2.me/theorems/37eff138-b2aa-4c0a-acfd-4aa6c3f2a91e
-- title:
--   Lemma 15 — AERM + on-average generalization ⇒ consistency with rate ε_oag + ε_erm
-- statement:
--   Let $(\mathcal H,\mathcal Z,f)$ be a learning problem with $\mathcal H$ nonempty and $|f(h;z)|\le B$, and let $\mathcal D$ be a probability measure on $\mathcal Z$. If a learning rule $A$ is an AERM with rate $\varepsilon_{\mathrm{erm}}(m)$ under $\mathcal D$ and on-average generalizes with rate $\varepsilon_{\mathrm{oag}}(m)$ under $\mathcal D$, then $A$ is consistent under $\mathcal D$ with rate $\varepsilon_{\mathrm{oag}}(m)+\varepsilon_{\mathrm{erm}}(m)$:
--   $$\mathbb E_{S\sim\mathcal D^m}\big[F(A(S))-F^*\big]\le\varepsilon_{\mathrm{oag}}(m)+\varepsilon_{\mathrm{erm}}(m)\qquad(m\ge1).$$
--
--   For an ERM this gives the implication from (on-average) generalization to consistency in Theorem 31.
--
--   **Formalization Note.** Standing assumptions made explicit as in Lemma 14: $\mathcal H$ nonempty, $|f|\le B$, measurability of each $f(h;\cdot)$, of the rule, and of the ERM value.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2651, Lemma 15

import Mathlib
import Definitions.Def_LearnStability_ERMLOO_Setting
import Definitions.Def_LearnStability_ERMLOO_RuleProperties

open MeasureTheory

namespace LearnStability.ERMLOO
theorem lemma15 {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hf : StandingAssumptions f B) (herm : MeasurableERMValue f)
    (A : Rule H Z) (hA : MeasurableRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (εerm εoag : ℕ → ℝ)
    (hAERM : IsAERM f A D εerm) (hoag : OnAverageGeneralizes f A D εoag) :
    Consistent f A D (fun m => εoag m + εerm m) := by sorry

end LearnStability.ERMLOO
