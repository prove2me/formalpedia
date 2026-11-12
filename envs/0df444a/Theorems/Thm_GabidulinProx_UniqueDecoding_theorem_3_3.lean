-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_theorem_3_3
-- name    : GabidulinProx.UniqueDecoding.theorem_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:52.515834+00:00
-- url     : https://prove2.me/theorems/24aa0313-4e07-4391-a7a1-7af940672d45
-- title:
--   Theorem 3.3 — correlated agreement and closeness of the entire line
-- statement:
--   Let $C=G(A,k)\le L^n$ be a Gabidulin code over finite fields $K\subseteq L$, where $q=|K|$, $1\le k\le n$, and the evaluation points are $K$-linearly independent. Let $1\le e$ and $2e<n-k+1$. Define $\sigma_r=\sum_{i=0}^rq^i$ and $\tau_e=(\sigma_e-1)+\sigma_e((\sigma_e-1)\sigma_{k-1}+1)$. For arbitrary $u_0,u_1\in L^n$, if
--
--   $$\Pr_{z\in L}[d(u_0+zu_1,C)\le e]>\frac{\tau_e}{|L|},$$
--
--   then both conclusions hold:
--
--   $$d([u_0,u_1],C^2)\le e,\qquad \forall z\in L,\ d(u_0+zu_1,C)\le e.$$
--
--   Probability is uniform on all of $L$. The first conclusion uses the rank of a stacked residual pair and therefore carries the correlation needed for the second conclusion.
--
--   Differences from the source:
--   - encoding: finite fields $\mathbb F_q\subseteq\mathbb F_{q^m}$ → finite fields $K,L$ with an algebra embedding, $q=|K|$ and $m=[L:K]$; reason: finite extensions have the specified cardinality; independence of the evaluation points implies $n\le m$
--   - encoding: coordinates numbered $1,\ldots,n$ and $q$-degree $<k$ → coordinates indexed by $\mathrm{Fin}\,n$ and polynomials represented as $\sum_{i<k}c_iX^{q^i}$; reason: the reindexing and coefficient representation preserve every polynomial, including zero
--   - encoding: rank after expanding in a fixed base-field basis → $K$-dimension of the span of the columns, in $L$ or $L\times L$; reason: this is the same matrix rank independently of the chosen basis
--   - encoding: minimum distance to a code and its order-two interleaving → finite minima over a linear submodule $C$ and pairs in $C\times C$; reason: both indexing types are finite and nonempty because zero is a codeword; the pair uses joint column rank
--   - encoding: minimum distance $d=n-k+1$ and uniform denominator $q^m$ → $d$ is substituted by $n-k+1$ and the denominator is $|L|$; reason: the paper fixes the Gabidulin distance, and $|L|=|K|^{[L:K]}$
--   - encoding: every point $x$ of the line $\ell_{u_0,u_1}$ → every parameter $z\in L$, through the point $u_0+zu_1$; reason: the line is by definition the image of this parameterization
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), Theorem 3.3 p.19; proof pp.23–24. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf

import Definitions.Def_GabidulinProx_UniqueDecoding_Codes

namespace GabidulinProx.UniqueDecoding

/-- Theorem 3.3, p.19, including its consequence for every point on the line. -/
theorem theorem_3_3 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L]
    [Algebra K L] {n k e : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (he : 1 ≤ e)
    (hdec : 2 * e < n - k + 1) (α : Fin n → L) (hα : LinearIndependent K α)
    (u₀ u₁ : Fin n → L)
    (hprob : uniformFraction (fun z => codeDistance K (gabidulin K α k) (linePoint u₀ u₁ z) ≤ e) >
      (tau (Fintype.card K) k e : ℝ) / (Fintype.card L : ℝ)) :
    pairDistance K (gabidulin K α k) u₀ u₁ ≤ e ∧
      ∀ z : L, codeDistance K (gabidulin K α k) (linePoint u₀ u₁ z) ≤ e := by sorry

end GabidulinProx.UniqueDecoding
