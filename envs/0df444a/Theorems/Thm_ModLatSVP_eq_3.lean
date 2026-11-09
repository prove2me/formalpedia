-- Prove2me | Theorems.Thm_ModLatSVP_eq_3
-- name    : ModLatSVP.eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:11:41.938138+00:00
-- url     : https://prove2.me/theorems/8110c638-7c04-4d5f-a669-acee3f4ae73e
-- title:
--   (3) — Banaszczyk's transference bound as printed: $\mu(L)\lambda_1(L^*)\le 2m$
-- statement:
--   Let $L$ be an $m$-dimensional Euclidean lattice, $m\ge1$, with dual lattice $L^*$ (taken in the span of $L$) and covering radius $\mu(L)=\sup_{t\in\mathrm{span}_{\mathbb R}L}\mathrm{dist}(t,L)$. Then
--
--   $$\mu(L)\,\lambda_1(L^*)\le 2m .$$
--
--   The paper cites this transference bound [Ban93] and uses it to turn a short dual vector into a covering-radius bound, which gives the computable search radius of the CVP algorithm and the last inequality of Lemma 2.1. Banaszczyk's theorem in fact gives $m/2$; the constant $2m$ is the paper's.
--
--   Differences from the source:
--   - encoding: an m-dimensional lattice L = B_L ℤ^m with linearly independent columns, its dual in span_ℝ(L) and its covering radius → a positive definite real Gram matrix G on Fin m; L* and µ in coefficients of the span (lam1Dual G, covRad G); reason: every such lattice has the positive definite Gram matrix B_Lᵀ B_L and every positive definite G is a Gram matrix (Cholesky), with the same λ₁(L*) and µ(L)
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), (3), §2.1, p.12 (PDF p.12); cited from W. Banaszczyk, Math. Ann. 296 (1993)

import Mathlib
import Definitions.Def_ModLatSVP_lam1

namespace ModLatSVP

/-- **(3), §2.1, p.12: Banaszczyk's transference bound, as printed.** Kim, Lee, Son, *Exact SVP and CVP
in Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript
sha256 e7151fad…): "Banaszczyk's transference theorem [Ban93] gives µ(L)λ₁(L*) ≤ 2m."

For every `m`-dimensional Euclidean lattice `L` (`m ≥ 1`), given by a positive definite Gram matrix `G`,
the covering radius and the minimum of the dual lattice satisfy `µ(L) λ₁(L*) ≤ 2m`.

**Formalization Note.** The paper cites the result and does not prove it; the constant `2m` is the
printed one (Banaszczyk's theorem gives `m/2`, so the printed form is weaker and true). -/
theorem eq_3 (m : ℕ) (hm : 1 ≤ m) (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.PosDef) :
    covRad G * lam1Dual G ≤ 2 * m := by sorry

end ModLatSVP
