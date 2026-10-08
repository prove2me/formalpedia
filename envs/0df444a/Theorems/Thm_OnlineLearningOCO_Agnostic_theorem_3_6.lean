-- Prove2me | Theorems.Thm_OnlineLearningOCO_Agnostic_theorem_3_6
-- name    : OnlineLearningOCO.Agnostic.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:28.342112+00:00
-- url     : https://prove2.me/theorems/e3d62cae-d7fd-49e1-8be8-f102cc1cf892
-- title:
--   Theorem 3.6 (upper bound) — a class of Littlestone dimension L has agnostic online regret at most 2√(L·ln(eT/L)·T)
-- statement:
--   Consider online classification with labels in $\{0,1\}$ and randomized predictions: on round $t$ the learner receives $x_t \in X$, predicts $p_t \in [0,1]$ (the probability of predicting $1$), then receives $y_t \in \{0,1\}$ and pays $|p_t - y_t|$. The prediction $p_t$ may depend on the past examples $(x_1,y_1),\dots,(x_{t-1},y_{t-1})$ and on $x_t$ only.
--
--   Let $H \subseteq \{0,1\}^X$ be a hypothesis class with finite Littlestone dimension $L = \operatorname{Ldim}(H)$, and let $T \ge L$. Then there is an online learner such that for every $h \in H$ and every sequence $(x_1,y_1),\dots,(x_T,y_T)$ of $T$ examples,
--
--   $$
--   \sum_{t=1}^T |p_t - y_t| - \sum_{t=1}^T |h(x_t) - y_t| \le 2\sqrt{L \,\ln\!\Big(\frac{eT}{L}\Big)\, T}.
--   $$
--
--   This is the upper-bound half of the characterization of agnostic online learnability by the Littlestone dimension: a class with finite $\operatorname{Ldim}$ admits sublinear regret against its best hypothesis, even though no realizability assumption is made on the labels.
--
--   **Formalization Note** The paper writes $O(\sqrt{\operatorname{Ldim}(H)\ln(T)\,T})$; its proof (Weighted Majority with $\eta = \sqrt{\log(d)/T}$ over the experts Expert$(i_1,\dots,i_\ell)$, $\ell \le L$, Corollary 3.8, Theorem 3.1 and (3.1)) yields the explicit bound $2\sqrt{L\ln(eT/L)\,T}$ stated here. The learner may depend on $H$ and $T$, as the paper's does. The horizon restriction $T \ge L$ is needed for this explicit expression (for $T < L$ the logarithm can be negative). For $L = 0$ the right side is $0$ (in Lean the product is $0 \cdot \ln(\cdot) = 0$), and the claim is that the regret is at most $0$, which holds. The lower bound $\Omega(\sqrt{\operatorname{Ldim}(H)\,T})$ of the theorem is proved in a cited reference and is not part of this statement.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 165, Theorem 3.6 (upper bound; proof pp. 166–168)

import Mathlib
import Definitions.Def_UnderstandingML_Online

namespace OnlineLearningOCO.Agnostic

open UnderstandingML

/-- Theorem 3.6, upper bound, p. 165, with the explicit constant of its proof (pp. 166–168). For
any hypothesis class `H` with `Ldim(H) = L < ∞` and any horizon `T ≥ L`, there is an online
learner with predictions `p_t ∈ [0,1]` (it sees only the past examples and the current instance)
such that for every `h ∈ H` and every sequence of `T` examples,
`∑_t |p_t − y_t| − ∑_t |h(x_t) − y_t| ≤ 2 √(L · ln(eT/L) · T)`.
At `L = 0` the right side is `0` (Lean: `0 * _ = 0`), and the claim is regret `≤ 0`. -/
theorem theorem_3_6 {X : Type*} (H : Set (X → Bool)) (L : ℕ) (hL : ldim H = L) (T : ℕ)
    (hLT : L ≤ T) :
    ∃ A : OnlineAlgR X, (∀ hist x, A hist x ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ (S : Fin T → X × Bool), ∀ h ∈ H,
        cumLoss A S - cumLossHyp h S ≤
          2 * Real.sqrt (L * Real.log (Real.exp 1 * T / L) * T) := by sorry

end OnlineLearningOCO.Agnostic
