-- Prove2me | Theorems.Thm_LearnStability_ERMLOO_lemma17
-- name    : LearnStability.ERMLOO.lemma17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:44:26.582735+00:00
-- url     : https://prove2.me/theorems/681bbb8d-0180-416d-b976-9aba23df78dd
-- title:
--   Lemma 17 — Eq. (12) + AERM + consistency ⇒ generalization with rate ε_emp + ε_erm + ε_cons
-- statement:
--   Let $(\mathcal H,\mathcal Z,f)$ be a learning problem with $\mathcal H$ nonempty and $|f(h;z)|\le B$, and let $\mathcal D$ be a probability measure on $\mathcal Z$. Suppose that Eq. (12) holds under $\mathcal D$ with rate $\varepsilon_{\mathrm{emp}}(m)$, i.e.
--   $$\mathbb E_{S\sim\mathcal D^m}\big[|F_S(\hat h_S)-F^*|\big]\le\varepsilon_{\mathrm{emp}}(m)\qquad(m\ge1),$$
--   and that a learning rule $A$ is an AERM with rate $\varepsilon_{\mathrm{erm}}(m)$ and consistent with rate $\varepsilon_{\mathrm{cons}}(m)$ under $\mathcal D$. Then $A$ generalizes under $\mathcal D$ with rate $\varepsilon_{\mathrm{emp}}(m)+\varepsilon_{\mathrm{erm}}(m)+\varepsilon_{\mathrm{cons}}(m)$.
--
--   Combined with Lemma 16, this gives the implication from universal consistency to universal generalization for an ERM in Theorem 31.
--
--   **Formalization Note.** Standing assumptions made explicit: $\mathcal H$ nonempty, $|f|\le B$, measurability of each $f(h;\cdot)$, of the rule and of the ERM value.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2653, Lemma 17

import Mathlib
import Definitions.Def_LearnStability_ERMLOO_Setting
import Definitions.Def_LearnStability_ERMLOO_RuleProperties

open MeasureTheory

namespace LearnStability.ERMLOO
theorem lemma17 {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hf : StandingAssumptions f B) (herm : MeasurableERMValue f)
    (A : Rule H Z) (hA : MeasurableRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (εemp εerm εcons : ℕ → ℝ)
    (h12 : ∀ m : ℕ, 1 ≤ m → ∫ S, |ermValue f S - optRisk f D| ∂(sampleLaw D m) ≤ εemp m)
    (hAERM : IsAERM f A D εerm) (hcons : Consistent f A D εcons) :
    Generalizes f A D (fun m => εemp m + εerm m + εcons m) := by sorry

end LearnStability.ERMLOO
