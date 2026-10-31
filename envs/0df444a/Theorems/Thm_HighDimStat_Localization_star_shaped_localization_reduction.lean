-- Prove2me | Theorems.Thm_HighDimStat_Localization_star_shaped_localization_reduction
-- name    : HighDimStat.Localization.star_shaped_localization_reduction
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T22:21:46.005653+00:00
-- url     : https://prove2.me/theorems/eff5927b-ccc8-46b2-b57c-dcbeba9fd675
-- title:
--   Star-shaped localization reduction for empirical $L^2$ deviation bounds
-- statement:
--   Let $(X, \mathcal{A}, \mu)$ be a measure space, let $x_1, \dots, x_n \in X$ be a fixed sample of $n$ points, and write
--   $$
--   \|f\|_2^2 := \int_X f(x)^2\,d\mu(x), \qquad \|f\|_2 := \sqrt{\|f\|_2^2}, \qquad \|f\|_n^2 := \frac{1}{n}\sum_{i=1}^n f(x_i)^2
--   $$
--   for the population and empirical $L^2$ squared norms of a function $f : X \to \mathbb{R}$. Let $\mathcal{F}$ be a class of real-valued functions on $X$ that is star-shaped around the origin, meaning that $\alpha f \in \mathcal{F}$ for all $f \in \mathcal{F}$ and $\alpha \in [0, 1]$, and let $t > 0$ be a localization radius. If the localized uniform deviation bound
--   $$
--   \big|\|g\|_n^2 - \|g\|_2^2\big| \le \frac{t^2}{2}
--   $$
--   holds for every $g \in \mathcal{F}$ with $\|g\|_2 \le t$, then the two-sided unlocalized deviation bound
--   $$
--   \big|\|f\|_n^2 - \|f\|_2^2\big| \le \frac{1}{2}\|f\|_2^2 + \frac{t^2}{2}
--   $$
--   holds simultaneously for every $f \in \mathcal{F}$.
--
--   This deterministic rescaling lemma is the core localization transfer step in the proof of Wainwright's Theorem 14.1, reducing global control of $|\|f\|_n^2 - \|f\|_2^2|$ over an entire star-shaped class $\mathcal{F}$ to control on the localized ball $\{g \in \mathcal{F} : \|g\|_2 \le t\}$.
--
--   **Formalization Note** The population and empirical squared norms, population norm, and star-shapedness predicate are imported from `Definitions.Def_HighDimStat_Localization_Core` (`popNormSq`, `popNorm`, `empiricalNormSq`, and `IsStarShapedAroundOrigin`).
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, Section 14.1.2, p. 456 (PDF p. 476), proof of Theorem 14.1, Eq. (14.5)

import Mathlib
import Definitions.Def_HighDimStat_Localization_Core

namespace HighDimStat.Localization

open MeasureTheory

theorem star_shaped_localization_reduction {X : Type*} [MeasurableSpace X] {n : ℕ}
    (xs : Fin n → X) (μ : Measure X) (F : Set (X → ℝ))
    (hStar : IsStarShapedAroundOrigin F) (t : ℝ) (ht : 0 < t)
    (h_loc : ∀ g ∈ F, popNorm μ g ≤ t →
      |empiricalNormSq xs g - popNormSq μ g| ≤ t ^ 2 / 2) :
    ∀ f ∈ F, |empiricalNormSq xs f - popNormSq μ f| ≤
      (1 / 2) * popNormSq μ f + t ^ 2 / 2 := by sorry

end HighDimStat.Localization
