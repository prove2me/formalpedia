-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_rank_image
-- name    : GabidulinProx.UniqueDecoding.rank_image
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:48.590772+00:00
-- url     : https://prove2.me/theorems/627801c3-24ad-4456-8e07-4128eafac854
-- title:
--   §3.2, display (p. 19) — rank as interpolant image dimension
-- statement:
--   Let $q=|K|$ for finite fields $K\subseteq L$, and let $\alpha_1,\ldots,\alpha_n$ be $K$-linearly independent with $n\ge1$. Put $V=\operatorname{span}_K\{\alpha_r\}$. Let $y_0,y_1\in L^n$ and let $\widehat y_0,\widehat y_1\in\mathcal L(q,m,n)$ interpolate their values at the evaluation points. Then both identities hold:
--
--   $$\operatorname{rk}_q(y_0)=\dim_K\widehat y_0(V),$$
--   $$\operatorname{rk}_q\begin{pmatrix}y_0\\y_1\end{pmatrix}
--   =\dim_K\{(\widehat y_0(x),\widehat y_1(x)):x\in V\}.$$
--
--   The images are $K$-subspaces because evaluation of a $q$-linearized polynomial is $K$-linear. These identities connect residual word ranks to dimensions on the evaluation span.
--
--   Differences from the source:
--   - encoding: finite fields $\mathbb F_q\subseteq\mathbb F_{q^m}$ → finite fields $K,L$ with an algebra embedding, $q=|K|$ and $m=[L:K]$; reason: finite extensions have the specified cardinality; independence of the evaluation points implies $n\le m$
--   - encoding: coordinates numbered $1,\ldots,n$ and $q$-degree $<k$ → coordinates indexed by $\mathrm{Fin}\,n$ and polynomials represented as $\sum_{i<k}c_iX^{q^i}$; reason: the reindexing and coefficient representation preserve every polynomial, including zero
--   - encoding: rank after expanding in a fixed base-field basis → $K$-dimension of the span of the columns, in $L$ or $L\times L$; reason: this is the same matrix rank independently of the chosen basis
--   - encoding: dimensions of images under the unique interpolants → dimensions of their $K$-spans, with the interpolants supplied by their membership and evaluation equations; reason: the image sets are already subspaces and interpolation is unique, so neither choice changes any value
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), §3.2, display following Theorem 3.3 p.19. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf

import Definitions.Def_GabidulinProx_UniqueDecoding_Codes

namespace GabidulinProx.UniqueDecoding

/-- Both rank-image identities in §3.2, p.19. The spans of the image sets are
written explicitly; evaluation of a q-polynomial is K-linear, so these are the images. -/
theorem rank_image {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L]
    [Algebra K L] {n : ℕ} (hn : 1 ≤ n) (α : Fin n → L) (hα : LinearIndependent K α)
    (y₀ y₁ : Fin n → L) (f₀ f₁ : Polynomial L)
    (hf₀ : IsLinearized (Fintype.card K) n f₀)
    (hf₁ : IsLinearized (Fintype.card K) n f₁)
    (hy₀ : ∀ r, f₀.eval (α r) = y₀ r) (hy₁ : ∀ r, f₁.eval (α r) = y₁ r) :
    wordRank K y₀ = Module.finrank K (Submodule.span K
      (f₀.eval '' (Submodule.span K (Set.range α) : Set L))) ∧
    pairRank K y₀ y₁ = Module.finrank K (Submodule.span K
      ((fun x => (f₀.eval x, f₁.eval x)) '' (Submodule.span K (Set.range α) : Set L))) := by sorry

end GabidulinProx.UniqueDecoding
