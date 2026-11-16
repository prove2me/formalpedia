-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_Supplement_theorem_4_1
-- name    : MaxCutSample2027.Coreset.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:05:23.807045+00:00
-- url     : https://prove2.me/theorems/07475b31-ccbe-4f70-a5f2-64eb7365f13a
-- title:
--   Theorem 4.1 — importance-sampling lower bound
-- statement:
--   Set $c=1/5184$ and $\varepsilon_0=1/(4\cdot512^2)$. Let $0<\varepsilon\le\varepsilon_0$, let $k$ be an integer with $1\le k\le c\varepsilon^{-2}$, and let $n>0$ be divisible by six. The graph $G_{n,k}$ is the balanced complete bipartite graph when $k<512$ and the balanced complete tripartite graph when $k\ge512$, with unit weights. Use importance sampling $p_v=d(v)/\sum_ud(u)$, independent draws with replacement, and $\widehat A_{ij}=A_{X_iX_j}/(k^2p_{X_i}p_{X_j})$. Then
--   $$\Pr\left(|\operatorname{MaxCut}(\widehat A)-\operatorname{MaxCut}(A)|>\varepsilon n^2\right)>\frac38.$$
--   This is the source's explicit worst-case lower bound for the importance-sampling estimator, retaining both strict inequalities and both graph regimes.
--
--   Differences from the source:
--   - encoding: the probability of a sample event under independent draws with replacement → the finite product-law average of its indicator over Fin k sample positions; reason: each ordered sample has exactly its source probability, and the event retains the source strict or non-strict inequalities
--   - encoding: balanced graphs with n vertices and named parts → Fin n with consecutive balanced parts and importanceLaw = d/D; reason: a relabeling of the same graphs; the switch at 512 and the degree-proportional law are preserved
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Theorem 4.1, p. 19. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7; printed page = PDF page).

import Definitions.Def_MaxCutSample2027_Coreset_Supplement_sampling
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset.Supplement

theorem theorem_4_1 (ε : ℝ) (hε : 0 < ε) (hε0 : ε ≤ 1 / (4 * (512 : ℝ) ^ 2))
    (k : ℕ) (hk : 1 ≤ k) (hsize : (k : ℝ) ≤ (1 / 5184 : ℝ) * ε ^ (-2 : ℤ))
    (n : ℕ) (hn : 0 < n) (hdiv : 6 ∣ n) :
    (3 : ℝ) / 8 < eventProbability (importanceLaw (lowerBoundGraph n k)) k
      (fun x => ε * (n : ℝ) ^ 2 <
        |maxCut (Ahat (lowerBoundGraph n k) (importanceLaw (lowerBoundGraph n k)) x) -
          maxCut (lowerBoundGraph n k)|) := by sorry

end MaxCutSample2027.Coreset.Supplement
