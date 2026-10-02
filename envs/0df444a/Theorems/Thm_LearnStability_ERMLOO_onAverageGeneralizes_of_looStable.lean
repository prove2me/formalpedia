-- Prove2me | Theorems.Thm_LearnStability_ERMLOO_onAverageGeneralizes_of_looStable
-- name    : LearnStability.ERMLOO.onAverageGeneralizes_of_looStable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T18:58:48.525981+00:00
-- url     : https://prove2.me/theorems/5e295723-5642-49bf-a2d1-50b97e80254a
-- title:
--   Proof of Theorem 31, second display — a LOO stable ERM on-average generalizes at size m − 1 with rate ε_stable(m) + 2B/m (corrected)
-- statement:
--   Let $(\mathcal H,\mathcal Z,f)$ be a learning problem with $\mathcal H$ nonempty and $|f(h;z)|\le B$, let $\mathcal D$ be a probability measure on $\mathcal Z$, and let $A$ be an ERM learning rule that is LOO stable with rate $\varepsilon_{\mathrm{stable}}(m)$ under $\mathcal D$. Then $A$ on-average generalizes on samples of size $m-1$ with rate $\varepsilon_{\mathrm{stable}}(m)+2B/m$: for every $n\ge1$,
--   $$\Big|\mathbb E_{S\sim\mathcal D^{n}}\big[F(A(S))-F_S(A(S))\big]\Big|\le\varepsilon_{\mathrm{stable}}(n+1)+\frac{2B}{n+1}.$$
--
--   This is the implication from LOO stability to on-average generalization in Theorem 31.
--
--   **Correction.** The printed chain on p. 2668 bounds the quantity by $|\cdots|+2B/m$, then writes the next line as an equality without the $2B/m$ term and concludes $\le\varepsilon_{\mathrm{stable}}(m)$. The argument proves $\varepsilon_{\mathrm{stable}}(m)+2B/m$, which is stated here. The difference does not affect Theorem 31, which states no rates.
--
--   **Formalization Note.** The rule $A$ is measurable and $f(h;\cdot)$ is measurable for each $h$. With $m=n+1$ no natural-number subtraction appears.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2668, proof of Theorem 31, second display (corrected: + 2B/m)

import Mathlib
import Definitions.Def_LearnStability_ERMLOO_Setting
import Definitions.Def_LearnStability_ERMLOO_RuleProperties

open MeasureTheory

namespace LearnStability.ERMLOO
theorem onAverageGeneralizes_of_looStable {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hf : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A) (hERM : IsERMRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (εstable : ℕ → ℝ)
    (hstable : LOOStable f A D εstable) :
    OnAverageGeneralizes f A D (fun n => εstable (n + 1) + 2 * B / (n + 1)) := by sorry

end LearnStability.ERMLOO
