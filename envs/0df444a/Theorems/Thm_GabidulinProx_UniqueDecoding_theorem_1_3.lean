-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_theorem_1_3
-- name    : GabidulinProx.UniqueDecoding.theorem_1_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:55.521072+00:00
-- url     : https://prove2.me/theorems/fa7679e6-4a67-4259-97e1-4314dc30944f
-- title:
--   Theorem 1.3 — the unique-decoding proximity gap with exact error
-- statement:
--   Let $L/K$ be a finite extension of finite fields, write $q=|K|$ and $m=[L:K]$, and let $C=G(A,k)\le L^n$ be a Gabidulin code with $1\le k\le n$ and $K$-linearly independent evaluation points. Its distance is $d=n-k+1$. For every real number
--
--   $$0<\delta\le\frac{d-1}{2n},\qquad e=\lfloor\delta n\rfloor,$$
--
--   put $\sigma_r=\sum_{i=0}^rq^i$ and $\tau_e=(\sigma_e-1)+\sigma_e((\sigma_e-1)\sigma_{k-1}+1)$. Then $C$ has a $(\delta,\varepsilon_e)$ proximity gap for lines in the sense of Definition 1.1, with
--
--   $$\varepsilon_e=\frac{\tau_e}{q^m}\le\frac{10q^{n-1}}{q^m},\qquad \tau_e\le10q^{n-1}.$$
--
--   Explicitly, for all $u_0,u_1\in L^n$, a uniform probability strictly greater than $\varepsilon_e$ that $u_0+zu_1$ has relative distance at most $\delta$ implies that the stacked pair has relative distance at most $\delta$ from $C^2$. The statement includes $e=0$, where $\tau_0=1$, and makes no restriction on the dependence of the two words or on whether the error threshold exceeds one. It is the full headline result, including the exact error formula and the explicit numerical bound.
--
--   Differences from the source:
--   - encoding: finite fields $\mathbb F_q\subseteq\mathbb F_{q^m}$ → finite fields $K,L$ with an algebra embedding, $q=|K|$ and $m=[L:K]$; reason: finite extensions have the specified cardinality; independence of the evaluation points implies $n\le m$
--   - encoding: coordinates numbered $1,\ldots,n$ and $q$-degree $<k$ → coordinates indexed by $\mathrm{Fin}\,n$ and polynomials represented as $\sum_{i<k}c_iX^{q^i}$; reason: the reindexing and coefficient representation preserve every polynomial, including zero
--   - encoding: rank after expanding in a fixed base-field basis → $K$-dimension of the span of the columns, in $L$ or $L\times L$; reason: this is the same matrix rank independently of the chosen basis
--   - encoding: minimum distance to a code and its order-two interleaving → finite minima over a linear submodule $C$ and pairs in $C\times C$; reason: both indexing types are finite and nonempty because zero is a codeword; the pair uses joint column rank
--   - encoding: minimum distance $d=n-k+1$ and uniform denominator $q^m$ → $d$ is substituted by $n-k+1$ and the denominator is $|L|$; reason: the paper fixes the Gabidulin distance, and $|L|=|K|^{[L:K]}$
--   - encoding: real $\delta$ with $e=\lfloor\delta n\rfloor$ and upper radius $(d-1)/(2n)$ → natural floor of the positive real $\delta n$, and upper radius $(n-k)/(2n)$; reason: $n\ge1$ follows from $1\le k\le n$, so natural floor equals the nonnegative integer floor and $d-1=n-k$ exactly
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), Theorem 1.3 p.5; Definition 1.1 p.4; body Theorem 3.3 p.19; Remark 3.8 p.24. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf

import Definitions.Def_GabidulinProx_UniqueDecoding_Codes

namespace GabidulinProx.UniqueDecoding

/-- Theorem 1.3, p.5, at full strength: every real radius, e=0 included,
exact error τ_e/|L| and the bound τ_e≤10q^(n-1). Here |L|=q^[L:K]. -/
theorem theorem_1_3 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L]
    [Algebra K L] {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (α : Fin n → L) (hα : LinearIndependent K α)
    (δ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ ((n - k : ℕ) : ℝ) / (2 * (n : ℝ))) :
    let e := ⌊δ * (n : ℝ)⌋₊
    HasProximityGap K (gabidulin K α k) δ
      ((tau (Fintype.card K) k e : ℝ) / (Fintype.card L : ℝ)) ∧
    tau (Fintype.card K) k e ≤ 10 * Fintype.card K ^ (n - 1) ∧
    (tau (Fintype.card K) k e : ℝ) / (Fintype.card L : ℝ) ≤
      (10 * Fintype.card K ^ (n - 1) : ℕ) / (Fintype.card L : ℝ) := by sorry

end GabidulinProx.UniqueDecoding
