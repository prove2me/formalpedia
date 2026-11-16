-- Prove2me | Theorems.Thm_IsingVectorBalancing_Subgaussian_Supplement_lemma_10
-- name    : IsingVectorBalancing.Subgaussian.Supplement.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:18:41.771421+00:00
-- url     : https://prove2.me/theorems/a48b8b4d-f88f-4481-8aef-ec475b59fa0a
-- title:
--   Lemma 10 — Approximate tensorization of variance under every external field
-- statement:
--   Let $n\ge1$ and let $v_i$ be an admissible family of unit-ball vectors. Put $\alpha_0=\min_i(1-\|v_i\|_2^2)>0$. For any real external field $h$, let $\mu_h$ be the published tilted product law. For every real function $f$ on the sign cube, with $D_i=I-P_i$ the actual single-site conditional residual,
--
--   $$\operatorname{Var}_{\mu_h}(f)\le\frac1{\alpha_0}\sum_i\mathbb E_{\mu_h}[(D_i f)^2].$$
--
--   This approximate tensorization estimate supports the spectral-gap conclusion of Theorem 2. Neither independence nor a bound on the external field is assumed.
--
--   Differences from the source:
--   - encoding: finite sets [n] and [q], real Euclidean vectors and finite expectations → Fin indices, EuclideanSpace, and finite sums; reason: the carriers and values are unchanged; Bool encodes the binary signs when present
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), p. 11 (PDF 12), Lemma 10, (9); standing setup pp. 1, 6, 10; proof p. 15

import Definitions.Def_IsingVectorBalancing_Subgaussian_Supplement_VectorChain

open scoped BigOperators
set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian.Supplement

/-- Lemma 10, (9), p.11/PDF12. -/
theorem lemma_10 {n d : ℕ} (hn : 0 < n) (v : Fin n → Vec d)
    (hv : Admissible v) (hα : 0 < alpha0 v) (h : Fin n → ℝ)
    (f : Configuration n → ℝ) :
    variance v h f ≤ (1 / alpha0 v) *
      ∑ i : Fin n, expectation v h (fun σ => (binaryResidual (probability v h) i f σ) ^ 2) := by sorry

end IsingVectorBalancing.Subgaussian.Supplement
