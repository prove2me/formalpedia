-- Prove2me | Theorems.Thm_GivenDegreeSeq_GraphLimit_lemma_6_1
-- name    : GivenDegreeSeq.GraphLimit.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:09.821123+00:00
-- url     : https://prove2.me/theorems/5ae288c1-6aa1-4407-b551-93e61c17ef77
-- title:
--   Lemma 6.1 — $P(|t(H,G)-Et(H,G)|>\varepsilon)\le 2e^{-C\varepsilon^2n^2}$ for independent-edge random graphs
-- statement:
--   Let $H$ be a finite simple graph on $k$ vertices. There is a constant $C>0$, depending only on $H$, such that the following holds. Let $n\ge k$, let $(p_{ij})$ be numbers in $[0,1]$, and let $G$ be the random graph on $n$ vertices in which each pair $\{i,j\}$ is an edge with probability $p_{ij}$, independently. Then for every $\varepsilon>0$,
--   $$\mathbb P\big(|t(H,G)-\mathbb E\,t(H,G)|>\varepsilon\big)\le 2e^{-C\varepsilon^2n^2},$$
--   where $t(H,G)$ is the homomorphism density (1).
--
--   Homomorphism densities of independent-edge random graphs therefore concentrate at rate $e^{-cn^2}$, fast enough to survive conditioning on events of probability $e^{-o(n^2)}$, which is how the proof of Theorem 1.1 transfers it to uniformly random graphs with a given degree sequence.
--
--   **Formalization Note** "Size $\le n$" is read as $|V(H)|=k\le n$. The constant $C$ is chosen before $n$, $p$ and $\varepsilon$ (`∃ C > 0, ∀ n p ε`). The probability of the event is computed under the law `edgeModel p`, and $\mathbb E\,t(H,G)$ is the integral of $t(H,\cdot)$ under the same law.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 26, Lemma 6.1

import Mathlib
import Definitions.Def_GivenDegreeSeq_GraphLimit_HomDensity
import Definitions.Def_GivenDegreeSeq_GraphLimit_EdgeModel

namespace GivenDegreeSeq.GraphLimit

open MeasureTheory

/-- **Lemma 6.1** (Chatterjee–Diaconis–Sly, arXiv:1005.1136v5, p. 26). Let `H` be a finite simple
graph with `k ≤ n` vertices and `G` a random graph on `n` vertices with independent edges (pair
`{i, j}` present with probability `p_ij ∈ [0,1]`). Then for every `ε > 0`,
`P(|t(H, G) − E t(H, G)| > ε) ≤ 2 e^{−C ε² n²}`, where `C > 0` depends only on `H`
(it is chosen before `n`, `p` and `ε`). -/
theorem lemma_6_1 (k : ℕ) (H : SimpleGraph (Fin k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, k ≤ n → ∀ p : Fin n → Fin n → ℝ,
      (∀ i j, 0 ≤ p i j ∧ p i j ≤ 1) → ∀ ε : ℝ, 0 < ε →
        edgeModel p {G | ε < |homDensity H G - ∫ G', homDensity H G' ∂ edgeModel p|} ≤
          ENNReal.ofReal (2 * Real.exp (-C * ε ^ 2 * (n : ℝ) ^ 2)) := by sorry

end GivenDegreeSeq.GraphLimit
