-- Prove2me | Theorems.Thm_MatroidProphetKW_Single_proposition_1
-- name    : MatroidProphetKW.Single.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:53.641004+00:00
-- url     : https://prove2.me/theorems/007edf5c-6d41-4e2d-a5bd-e7e1317b3a7a
-- title:
--   Proposition 1 — $\alpha$-balanced thresholds give $\mathbb E[w(A)] \ge \frac1\alpha\,\mathrm{OPT}$ against online weight-adaptive adversaries
-- statement:
--   Let $\mathcal M = (\mathcal U, \mathcal I)$ be a matroid on a finite ground set, and for each $x \in \mathcal U$ let $F_x$ be a probability distribution supported on $[0,\infty)$ with finite mean. Let $w \sim \bigotimes_x F_x$ be the random weights and $\mathrm{OPT} = \mathbb E[\mathrm{OPT}(w)]$. Let a threshold rule have $\alpha$-balanced thresholds (Definition 1) for some $\alpha > 0$. Then for every online weight-adaptive adversary, the set $A$ selected by the rule on the input sequence revealed by the adversary satisfies
--   $$\mathbb E[w(A)] \;\ge\; \frac1\alpha\, \mathrm{OPT}. \tag{4}$$
--
--   Proposition 1 reduces the matroid prophet inequality to the design of thresholds satisfying the two deterministic-looking conditions (2)–(3); with $\alpha = 2$ it yields the main theorem.
--
--   **Formalization Note** "Monotone algorithm" means a threshold rule in the sense of the `Online` definition (non-negative thresholds depending measurably on the revealed prefix, $\infty$ on infeasible steps). The adversary is deterministic and measurable; randomized adversaries are mixtures of these. The expectation $\mathbb E[w(A)]$ is the Bochner integral of $w \mapsto w(A(\sigma(w)))$ over $\bigotimes_x F_x$, where $\sigma(w)$ is the input sequence the adversary reveals.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 6, Proposition 1, (4)

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Setting
import Definitions.Def_MatroidProphetKW_Single_Online
import Definitions.Def_MatroidProphetKW_Single_Balanced

namespace MatroidProphetKW.Single

open MeasureTheory

/-- Proposition 1 (Kleinberg–Weinberg, arXiv:1201.4764v1, p. 6): if a threshold rule has
`a`-balanced thresholds (Definition 1), then against every online weight-adaptive adversary
  `E[w(A)] ≥ (1/a) · OPT`.     (4) -/
theorem proposition_1 {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF0 : ∀ x, F x (Set.Iio 0) = 0) (hFi : ∀ x, Integrable id (F x))
    (Thr : Finset α → List α → (α → ℝ) → α → ℝ) (hThr : IsThresholdRule Thr)
    (a : ℝ) (ha : 0 < a) (hbal : Balanced M F Thr a)
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv) :
    (1 / a) * OPT M F ≤ ∫ w, wt w (run M Thr (advOrder adv w) w) ∂(Measure.pi F) := by sorry

end MatroidProphetKW.Single
