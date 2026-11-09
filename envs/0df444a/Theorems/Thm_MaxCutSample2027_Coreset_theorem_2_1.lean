-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_theorem_2_1
-- name    : MaxCutSample2027.Coreset.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:43:14.026139+00:00
-- url     : https://prove2.me/theorems/4e8fcea0-3927-424f-98b0-73ffc1a81e18
-- title:
--   Theorem 2.1 — sampling approximates the Max-Cut value
-- statement:
--   Let $V$ be a finite nonempty vertex set, $n=|V|$, and let $A:V\times V\to\mathbb R$ be symmetric with zero diagonal and nonnegative entries. Let $p$ satisfy $p_v>0$ for every vertex and $\sum_vp_v=1$. Define $K_{uv}=A_{uv}/(n^2p_up_v)$. Write $H=\sum_vp_v\sqrt{\sum_up_uK_{uv}^2}$.
--
--   For an integer $k\ge1$, let $X=(X_0,\ldots,X_{k-1})$ be independent draws with replacement from $p$, and let $P_X(v)=|\{i:X_i=v\}|/k$.
--
--   Define the matrix on the $k$ labelled sample positions by $\widehat A_{ij}=A_{X_iX_j}/(k^2p_{X_i}p_{X_j})$. For a finite matrix $B$ on vertices $W$, write $\operatorname{MaxCut}(B)=\max_{S\subseteq W}\sum_{u\in S,v\notin S}B_{uv}$. Then
--   $$\mathbb E_X\left|\frac{\operatorname{MaxCut}(\widehat A)-\operatorname{MaxCut}(A)}{n^2}\right|\le\frac{48H}{\sqrt{k}}.$$
--   The sampled maximum ranges over all subsets of $\operatorname{Fin}(k)$, retaining repeated vertices as distinct copies. This estimate applies to every nonnegative real weight matrix satisfying the stated symmetry and diagonal conditions and to every positive sampling distribution.
--
--   **Formalization Note** Cut values use a genuine finite maximum. The sample expectation is the explicit product law; no analytic integrability assumption is needed.
--
--   Differences from the source:
--   - generalization: the standing assumption d(v)>0 for every vertex → isolated vertices are allowed; reason: no quantity or step of §2.2–§2.4 divides by a degree; imposing positive degrees recovers every source instance
--   - encoding: iid sample expectation and Max-Cut over finite vertex subsets → the explicit product-law finite sum and a finite maximum over Finset subsets of V or Fin k; reason: the same outcomes, probabilities, and cuts are used; positivity of n and k preserves the normalization
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Theorem 2.1, equation (2.3), p. 6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7).

import Definitions.Def_MaxCutSample2027_Coreset_model
open scoped BigOperators

namespace MaxCutSample2027.Coreset

theorem theorem_2_1 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k) :
    sampleAverage p k (fun x =>
      |(maxCut (Ahat A p x) - maxCut A) / (Fintype.card V : ℝ) ^ 2|) ≤
      48 * H A p / Real.sqrt (k : ℝ) := by sorry

end MaxCutSample2027.Coreset
