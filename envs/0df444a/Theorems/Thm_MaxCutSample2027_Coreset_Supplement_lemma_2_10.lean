-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_Supplement_lemma_2_10
-- name    : MaxCutSample2027.Coreset.Supplement.lemma_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:00:51.987772+00:00
-- url     : https://prove2.me/theorems/4b73bb77-38e0-434a-b662-5f29aa85039d
-- title:
--   Lemma 2.10 — bounding H
-- statement:
--   Let $V$ be a finite nonempty set of size $n$, let $A$ be a symmetric nonnegative real matrix with zero diagonal, and let $p$ be a positive probability vector. Write $K_{uv}=A_{uv}/(n^2p_up_v)$ and $H=\sum_vp_v\sqrt{\sum_up_uK_{uv}^2}$. Sample positions are independent draws from $p$ with replacement; their empirical law is $P_X$, and the sampled graph on $[k]$ has weights $\widehat A_{ij}=A_{X_iX_j}/(k^2p_{X_i}p_{X_j})$. Assume also $A_{uv}\le1$ for all vertices. Then both statements hold:
--   $$H^2\le\frac1{n^3}\sum_v\frac{d(v)}{p_v},\qquad
--   \bigl(\forall v,\ p_v\ge d(v)/n^2\bigr)\Longrightarrow H\le1,$$
--   where $d(v)=\sum_uA_{vu}$. This relates the second-moment quantity to the sampling probabilities and supplies the bounded-weight sampling specializations.
--
--   Differences from the source:
--   - generalization: discard isolated vertices and assume d(v) > 0 in the standing setup → all symmetric nonnegative zero-diagonal matrices, including isolated vertices; reason: isolated vertices contribute zero; restricting to graphs with positive degrees recovers every source instance
--   - encoding: a finite vertex set of size n and finite matrix sums → Fintype V with n its cardinality; reason: this is the same finite matrix setup and normalization
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Lemma 2.10, p. 14. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7; printed page = PDF page).

import Definitions.Def_MaxCutSample2027_Coreset_Supplement_sampling
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset.Supplement

theorem lemma_2_10 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (hbound : ∀ u v, A u v ≤ 1) :
    H A p ^ 2 ≤ (∑ v, weightedDegree A v / p v) / (Fintype.card V : ℝ) ^ 3 ∧
    ((∀ v, weightedDegree A v / (Fintype.card V : ℝ) ^ 2 ≤ p v) → H A p ≤ 1) := by sorry

end MaxCutSample2027.Coreset.Supplement
