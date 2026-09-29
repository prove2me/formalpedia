-- Prove2me | Theorems.Thm_LearnStability_ERMLOO_lemma14
-- name    : LearnStability.ERMLOO.lemma14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:22:49.505797+00:00
-- url     : https://prove2.me/theorems/e4d182d4-3d83-486a-bc8a-f4e426f78410
-- title:
--   Lemma 14 — AERM + on-average generalization ⇒ generalization with rate ε_oag + 2ε_erm + 2B/√m
-- statement:
--   Let $(\mathcal H,\mathcal Z,f)$ be a learning problem with $\mathcal H$ nonempty and $|f(h;z)|\le B$, and let $\mathcal D$ be a probability measure on $\mathcal Z$. Let $A$ be a learning rule that is an AERM with rate $\varepsilon_{\mathrm{erm}}(m)$ under $\mathcal D$ and on-average generalizes with rate $\varepsilon_{\mathrm{oag}}(m)$ under $\mathcal D$. Then $A$ generalizes under $\mathcal D$ with rate
--   $$\varepsilon_{\mathrm{oag}}(m)+2\varepsilon_{\mathrm{erm}}(m)+\frac{2B}{\sqrt m},$$
--   that is, $\mathbb E_{S\sim\mathcal D^m}\big[|F(A(S))-F_S(A(S))|\big]\le\varepsilon_{\mathrm{oag}}(m)+2\varepsilon_{\mathrm{erm}}(m)+2B/\sqrt m$ for all $m\ge1$.
--
--   For an ERM ($\varepsilon_{\mathrm{erm}}=0$) this shows that on-average generalization and generalization are equivalent up to $2B/\sqrt m$, one of the links in the proof of Theorem 31.
--
--   **Formalization Note.** Standing assumptions made explicit: $\mathcal H$ nonempty, $|f|\le B$, each $f(h;\cdot)$ measurable, the rule $A$ measurable (joint measurability of $(S,z)\mapsto f(A(S);z)$) and the ERM value $S\mapsto\inf_hF_S(h)$ measurable. The rates $\varepsilon_{\mathrm{erm}},\varepsilon_{\mathrm{oag}}$ are arbitrary real sequences; no monotonicity is needed.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2651, Lemma 14

import Mathlib
import Definitions.Def_LearnStability_ERMLOO_Setting
import Definitions.Def_LearnStability_ERMLOO_RuleProperties

open MeasureTheory

namespace LearnStability.ERMLOO
theorem lemma14 {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hf : StandingAssumptions f B) (herm : MeasurableERMValue f)
    (A : Rule H Z) (hA : MeasurableRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (εerm εoag : ℕ → ℝ)
    (hAERM : IsAERM f A D εerm) (hoag : OnAverageGeneralizes f A D εoag) :
    Generalizes f A D (fun m => εoag m + 2 * εerm m + 2 * B / Real.sqrt m) := by sorry

end LearnStability.ERMLOO
