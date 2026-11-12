-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_lemma_2_7
-- name    : GabidulinProx.UniqueDecoding.lemma_2_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:38.78054+00:00
-- url     : https://prove2.me/theorems/f6562226-c757-45b5-8186-b87240f6c155
-- title:
--   Lemma 2.7 — Berlekamp–Welch reconstruction and unique recovery
-- statement:
--   Let $L/K$ be finite fields with $q=|K|$, let $1\le k\le n$, and let the evaluation points $\alpha_r$ be $K$-linearly independent. Fix $t\ge0$ with $2t<n-k+1$. Suppose $P\in\mathcal L(q,m,k)$ and $y=P(A)+\mathrm{err}$ with $\operatorname{rk}_q(\mathrm{err})\le t$. Then:
--
--   1. There exists a nonzero bounded-degree reconstruction pair $(A,B)$ solving Equation (6).
--   2. Specifically, for $W=\operatorname{span}_K\{\mathrm{err}_r\}$, the monic polynomial $\Lambda=\prod_{w\in W}(X-w)$ is nonzero and $(\Lambda,\Lambda\circ P)$ is such a pair, including both required degree bounds.
--   3. Every nonzero reconstruction pair of those degrees satisfies
--
--   $$B=A\circ P.$$
--
--   4. If another $P'\in\mathcal L(q,m,k)$ satisfies $B=A\circ P'$, then $P=P'$.
--
--   The lemma gives reconstruction solvability, the explicit error-space locator, and uniqueness of the recovered message rather than uniqueness of the homogeneous reconstruction pair.
--
--   Differences from the source:
--   - encoding: finite fields $\mathbb F_q\subseteq\mathbb F_{q^m}$ → finite fields $K,L$ with an algebra embedding, $q=|K|$ and $m=[L:K]$; reason: finite extensions have the specified cardinality; independence of the evaluation points implies $n\le m$
--   - encoding: coordinates numbered $1,\ldots,n$ and $q$-degree $<k$ → coordinates indexed by $\mathrm{Fin}\,n$ and polynomials represented as $\sum_{i<k}c_iX^{q^i}$; reason: the reindexing and coefficient representation preserve every polynomial, including zero
--   - encoding: rank after expanding in a fixed base-field basis → $K$-dimension of the span of the columns, in $L$ or $L\times L$; reason: this is the same matrix rank independently of the chosen basis
--   - encoding: minimum distance $d=n-k+1$ and uniform denominator $q^m$ → $d$ is substituted by $n-k+1$ and the denominator is $|L|$; reason: the paper fixes the Gabidulin distance, and $|L|=|K|^{[L:K]}$
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), Lemma 2.7 p.14; standing decoding radius and Equation (6) p.13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf

import Definitions.Def_GabidulinProx_UniqueDecoding_Reconstruction

namespace GabidulinProx.UniqueDecoding

/-- Lemma 2.7, p.14, including the standing radius 2t<d from p.13:
existence, the explicit annihilator solution, universal composition identity and recovery. -/
theorem lemma_2_7 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L]
    [Algebra K L] {n k t : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (ht : 2 * t < n - k + 1) (α : Fin n → L) (hα : LinearIndependent K α)
    (P : Polynomial L) (hP : IsLinearized (Fintype.card K) k P)
    (err y : Fin n → L) (hy : y = evaluateWord α P + err) (herr : wordRank K err ≤ t) :
    (∃ A B : Polynomial L, IsReconstruction (Fintype.card K) k t α y A B) ∧
    (let Λ := annihilator K (Submodule.span K (Set.range err))
     Λ.Monic ∧ Λ ≠ 0 ∧ IsReconstruction (Fintype.card K) k t α y Λ (Λ.comp P)) ∧
    (∀ A B : Polynomial L, IsReconstruction (Fintype.card K) k t α y A B → B = A.comp P) ∧
    (∀ A B P' : Polynomial L, IsReconstruction (Fintype.card K) k t α y A B →
      IsLinearized (Fintype.card K) k P' → B = A.comp P → B = A.comp P' → P = P') := by sorry

end GabidulinProx.UniqueDecoding
