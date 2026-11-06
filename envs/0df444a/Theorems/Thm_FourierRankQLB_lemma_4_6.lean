-- Prove2me | Theorems.Thm_FourierRankQLB_lemma_4_6
-- name    : FourierRankQLB.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:12.94161+00:00
-- url     : https://prove2.me/theorems/d35c1fde-9483-4006-808c-518200154d6a
-- title:
--   Lemma 4.6 — Rademacher moments
-- statement:
--   Let $u\in\mathbb R^d$ be a unit vector, let $v=d^{-1/2}(\sigma_1,\dots,\sigma_d)$ with independent uniform signs, and put $X=d(u^Tv)^2$. Then
--   $$
--   \mathbb EX=1,\qquad \mathbb EX^2=3-2\sum_{i=1}^du_i^4\le3 .
--   $$
--
--   These two moments feed the Paley–Zygmund bound on the negative determinant component.
--
--   Differences from the source:
--
--   - encoding: expectation over independent uniform signs → the finite average `signAvg`; reason: the law is uniform on a finite set; same values
--   - generalization: the standing assumption of §4.3 that $d\ge2$ is even → no hypothesis on $d$ (the unit vector $u$ forces $d\ge1$); reason: both moment identities hold for every $d\ge1$; even $d\ge2$ is a special case
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Lemma 4.6, p.28

import Mathlib
import Definitions.Def_FourierRankQLB_signObj
import Definitions.Def_FourierRankQLB_signAvg

open Matrix

namespace FourierRankQLB

/-- Lemma 4.6 (Rademacher moments). For a unit vector `u ∈ ℝ^d` and `X = d(uᵀv)²`, with `v` the
random normalized sign vector: `E X = 1` and `E X² = 3 - 2 ∑ u_i⁴ ≤ 3`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Lemma 4.6, p. 28. -/
theorem lemma_4_6 {d : ℕ} (u : Fin d → ℝ) (hu : ∑ i, u i ^ 2 = 1) :
    signAvg (fun σ => (d : ℝ) * (u ⬝ᵥ signObj σ) ^ 2) = 1 ∧
      signAvg (fun σ => ((d : ℝ) * (u ⬝ᵥ signObj σ) ^ 2) ^ 2) = 3 - 2 * ∑ i, u i ^ 4 ∧
      3 - 2 * ∑ i, u i ^ 4 ≤ 3 := by sorry

end FourierRankQLB
