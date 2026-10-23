-- Prove2me | Theorems.Thm_MFEUnique_Uniq_lemma_3
-- name    : MFEUnique.Uniq.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:20.461588+00:00
-- url     : https://prove2.me/theorems/d6c3ef7f-48a7-401e-8149-9bc91c703ae0
-- title:
--   Lemma 3, p. 36 — the optimal strategy correspondence G(x, s) is non-empty, compact-valued and upper hemicontinuous
-- statement:
--   Consider the anonymous stochastic game of `MFEUnique.Uniq.Game` under the standing assumptions ($p$ a probability vector, $0 < \beta < 1$, and Assumption 1: $\pi$ bounded and jointly continuous, $w$ jointly continuous, $X$ compact, $\Gamma$ compact-valued and continuous), and suppose every feasible set $\Gamma(x)$ is non-empty. Then the optimal stationary strategy correspondence
--   $$G(x, s) = \operatorname*{argmax}_{a \in \Gamma(x)} \; \pi(x, a, s) + \beta \sum_{j=1}^{J} p_j\, V(w(x, a, s, \zeta_j), s)$$
--   is non-empty and compact for every $(x, s) \in X \times \mathcal P(X)$, and the correspondence $(x, s) \mapsto G(x, s)$ is upper hemicontinuous on $X \times \mathcal P(X)$.
--
--   This is the well-posedness result behind the model: with $G$ single-valued it makes the optimal strategy $g$ continuous, and hence the kernel $Q_g$ and the operator $M_s$ well defined.
--
--   **Formalization Note** Non-emptiness of $\Gamma(x)$ is added: the paper writes $\Gamma : X \to 2^A$ and the lemma is false if some $\Gamma(x)$ is empty. Upper hemicontinuity is joint in $(x, s)$, as the proof of Theorem 3 uses it ("From Lemma 3, g is continuous", p. 37). $V$ is the paper's supremum over measurable strategies.
-- source:
--   Light and Weintraub, Mean Field Equilibrium: Uniqueness, Existence, and Comparative Statics, arXiv:1903.02273v3, p. 36, Lemma 3 (proof p. 37); also p. 11, first paragraph

import Mathlib
import Definitions.Def_MFEUnique_Uniq_Game

open MeasureTheory

namespace MFEUnique.Uniq

/-- Lemma 3 (Light–Weintraub, arXiv:1903.02273v3, p. 36): under Assumption 1 the optimal
strategy correspondence `G(x, s)` is non-empty, compact-valued and upper hemicontinuous (jointly
in `(x, s)`). The non-emptiness of every `Γ(x)` is implicit in `Γ : X → 2^A` and is added. -/
theorem lemma_3 {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {q J : ℕ} {A : Set (EuclideanSpace ℝ (Fin q))} {E : Type*} [TopologicalSpace E]
    (G : Game X q J E A) (hG : G.Standing) (hΓ : ∀ x, (G.Γ x).Nonempty) :
    (∀ (x : X) (s : ProbabilityMeasure X), (G.Gopt x s).Nonempty ∧ IsCompact (G.Gopt x s)) ∧
      UpperHemicontinuous (fun z : X × ProbabilityMeasure X => G.Gopt z.1 z.2) := by sorry

end MFEUnique.Uniq
