-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_Supplement_theorem_5_1
-- name    : MaxCutSample2027.Coreset.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:11:06.458413+00:00
-- url     : https://prove2.me/theorems/0fedf5cc-f967-48ef-97e9-b241ad2d5767
-- title:
--   Theorem 5.1 — sampling approximates the r-way Max-Cut value
-- statement:
--   Let $V$ be a finite nonempty set of size $n$, let $A$ be a symmetric nonnegative real matrix with zero diagonal, and let $p$ be a positive probability vector. Write $K_{uv}=A_{uv}/(n^2p_up_v)$ and $H=\sum_vp_v\sqrt{\sum_up_uK_{uv}^2}$. Sample positions are independent draws from $p$ with replacement; their empirical law is $P_X$, and the sampled graph on $[k]$ has weights $\widehat A_{ij}=A_{X_iX_j}/(k^2p_{X_i}p_{X_j})$. Let $r\ge2$ and $k\ge1$ be integers. For a symmetric matrix $B$ on a finite vertex set, let $\operatorname{MaxCut}_r(B)$ be the maximum of $\sum_{u,v:f(u)<f(v)}B_{uv}$ over all assignments $f$ to $r$ labels; empty parts are allowed. Then
--   $$\mathbb E\left|\frac{\operatorname{MaxCut}_r(\widehat A)-\operatorname{MaxCut}_r(A)}{n^2}\right|\le48\sqrt2H\sqrt{\frac{\log(2r)}k}.$$
--   The logarithm is natural. The sampled graph's optimum is over all assignments of its distinct $k$ positions. This extends the value approximation guarantee to r-way cuts without a weight bound or a uniform-sampling restriction.
--
--   Differences from the source:
--   - generalization: discard isolated vertices and assume d(v) > 0 in the standing setup → all symmetric nonnegative zero-diagonal matrices, including isolated vertices; reason: isolated vertices contribute zero; restricting to graphs with positive degrees recovers every source instance
--   - encoding: expectation under k independent vertex draws with replacement → the explicit finite product-law sum over Fin k sample positions; reason: the sum gives exactly the source sampling law, including distinct positions for repeated draws
--   - encoding: r-way cut values of a symmetric matrix → the published Max3CutHard cut maximum applied to the matrix edge-list adapter, with vertex types in Type; reason: each ordered pair carries half its matrix weight, giving exactly the sum over j < l by symmetry; Type represents every finite source vertex set
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Theorem 5.1, p. 23. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7; printed page = PDF page).

import Definitions.Def_MaxCutSample2027_Coreset_Supplement_rSigned
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset.Supplement

theorem theorem_5_1 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k)
    (r : ℕ) (hr : 2 ≤ r)
    : sampleAverage p k (fun x =>
        |(maxCutR r (Ahat A p x) - maxCutR r A) / (Fintype.card V : ℝ) ^ 2|) ≤
      48 * Real.sqrt 2 * H A p * Real.sqrt (Real.log (2 * (r : ℝ)) / (k : ℝ)) := by sorry

end MaxCutSample2027.Coreset.Supplement
