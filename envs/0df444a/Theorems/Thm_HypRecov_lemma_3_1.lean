-- Prove2me | Theorems.Thm_HypRecov_lemma_3_1
-- name    : HypRecov.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:36:12.191455+00:00
-- url     : https://prove2.me/theorems/a30a7523-e732-4e11-be46-c64511c1da81
-- title:
--   Lemma 3.1 — signed Boolean moments
-- statement:
--   Let $N,d\ge 0$ and let $\mu:\{0,1\}^N\to\mathbb R$ be nonzero. If all moments of $\mu$ of degree at most $d$ vanish,
--   $$\sum_{x\in\{0,1\}^N}\mu(x)\prod_{i\in B}x_i=0\qquad(B\subseteq[N],\ |B|\le d),$$
--   then each of $\{x:\mu(x)>0\}$ and $\{x:\mu(x)<0\}$ contains at least $2^d$ points.
--
--   This separate-sign bound is the base case for the crossing bound of Lemma 3.2.
--
--   Differences from the source:
--   - encoding: {0,1}^N, x_i ∈ {0,1} → Fin N → Bool, x_i read as 1 or 0; reason: Lean convention
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Lemma 3.1, p.6 (PDF p.7)

import Mathlib

namespace HypRecov

/-- **Lemma 3.1 (Signed Boolean moments).** Zhang, Chen, Shen, *Hypergraph Recovery from Anonymous
Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Lemma 3.1, p.6 (PDF p.7):
"Let µ : {0,1}^N → ℝ be nonzero and d ≥ 0. If Σ_x µ(x) Π_{i∈B} x_i = 0 (B ⊆ [N], |B| ≤ d), then
each of {x : µ(x) > 0} and {x : µ(x) < 0} contains at least 2^d points."

**Formalization Note.** `{0,1}^N` is `Fin N → Bool`, with `x_i` read as `1` or `0`. -/
theorem lemma_3_1 (N d : ℕ) (μ : (Fin N → Bool) → ℝ) (hμ : μ ≠ 0)
    (hmom : ∀ B : Finset (Fin N), B.card ≤ d →
      ∑ x, μ x * ∏ i ∈ B, (if x i then (1 : ℝ) else 0) = 0) :
    2 ^ d ≤ (Finset.univ.filter (fun x => 0 < μ x)).card ∧
      2 ^ d ≤ (Finset.univ.filter (fun x => μ x < 0)).card := by sorry

end HypRecov
