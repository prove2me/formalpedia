-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_lemma_3_7
-- name    : GabidulinProx.UniqueDecoding.lemma_3_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:27.636116+00:00
-- url     : https://prove2.me/theorems/63339b8e-8d5e-4070-b8af-3af2edd21b41
-- title:
--   Lemma 3.7 — a common subspace of dimension exactly n − e
-- statement:
--   Let $L/K$ be finite fields with $q=|K|$, and let $C=G(A,k)$ have independent evaluation points with $1\le k\le n$. Let $1\le e$ and $2e<n-k+1$. Fix words $u_0,u_1$, their unique interpolants $\widehat u_0,\widehat u_1\in\mathcal L(q,m,n)$, and the good-parameter set $S$. Let $a_0\in L[Z]$ with $\deg_Za_0\le\sigma_e-1$, and put $S_0=\{z\in S:a_0(z)\ne0\}$. Supply decoded messages $P_z$ on $S$ and a family $\widetilde P$ of $q$-degree less than $k$ satisfying the degree bound and pointwise identity of Lemma 3.6. If
--
--   $$|S_0|>\sigma_e((\sigma_e-1)\sigma_{k-1}+1),$$
--
--   then there exists a $K$-subspace $E\le V=\operatorname{span}_K A$ such that
--
--   $$\dim_KE=n-e,\qquad
--   \widetilde P(x,Z)=a_0(Z)^{\sigma_{k-1}}(\widehat u_0(x)+Z\widehat u_1(x))\quad(x\in E).$$
--
--   The equality holds in $L[Z]$, and the dimension is exact. This is common agreement across the parameter family, rather than a separate subspace for each $z$.
--
--   Differences from the source:
--   - encoding: finite fields $\mathbb F_q\subseteq\mathbb F_{q^m}$ → finite fields $K,L$ with an algebra embedding, $q=|K|$ and $m=[L:K]$; reason: finite extensions have the specified cardinality; independence of the evaluation points implies $n\le m$
--   - encoding: coordinates numbered $1,\ldots,n$ and $q$-degree $<k$ → coordinates indexed by $\mathrm{Fin}\,n$ and polynomials represented as $\sum_{i<k}c_iX^{q^i}$; reason: the reindexing and coefficient representation preserve every polynomial, including zero
--   - encoding: rank after expanding in a fixed base-field basis → $K$-dimension of the span of the columns, in $L$ or $L\times L$; reason: this is the same matrix rank independently of the chosen basis
--   - encoding: minimum distance to a code and its order-two interleaving → finite minima over a linear submodule $C$ and pairs in $C\times C$; reason: both indexing types are finite and nonempty because zero is a codeword; the pair uses joint column rank
--   - encoding: minimum distance $d=n-k+1$ and uniform denominator $q^m$ → $d$ is substituted by $n-k+1$ and the denominator is $|L|$; reason: the paper fixes the Gabidulin distance, and $|L|=|K|^{[L:K]}$
--   - encoding: bivariate $q$-linearized polynomials in $X$ with coefficients in $L[Z]$ → families of $X^{q^i}$-coefficients, with explicit specialization and evaluation maps; reason: these encode the same bivariate polynomials and retain polynomial rather than function identities
--   - encoding: polynomial degree bounds with zero polynomial of degree $-\infty$ → natural-degree inequalities against nonnegative bounds; reason: zero has natural degree zero and satisfies precisely the same upper bounds
--   - generalization: $\widetilde P$ is the polynomial obtained from Lemma 3.6 → any family with its degree bound and pointwise identity, together with the degree bound of $a_0$; reason: $a_0\ne0$ is implied by the hypothesis on $|S_0|$, since $a_0=0$ makes $S_0$ empty; the congruence modulo $S_0(Z)$, the other $a_i,b_j$, and their global reconstruction identity are unused in this lemma; every constructed source family satisfies the stated hypotheses
--   - encoding: the unique interpolants $\widehat u_0,\widehat u_1$ and the unique decoded $P_z$ → polynomials supplied by their membership, evaluation and residual-rank conditions; reason: Lemma 2.2 and $2e<d$ make them unique, so no value changes
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), Lemma 3.7 p.22; proof pp.22–23. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf

import Definitions.Def_GabidulinProx_UniqueDecoding_Reconstruction

namespace GabidulinProx.UniqueDecoding

/-- Lemma 3.7, p.22. Only the pointwise and degree conclusions of Lemma 3.6
are needed; no particular witness is chosen from that unproved lemma. -/
theorem lemma_3_7 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L]
    [Algebra K L] {n k e : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (he : 1 ≤ e)
    (hdec : 2 * e < n - k + 1) (α : Fin n → L) (hα : LinearIndependent K α)
    (u₀ u₁ : Fin n → L) (f₀ f₁ : Polynomial L)
    (hf₀ : IsLinearized (Fintype.card K) n f₀)
    (hf₁ : IsLinearized (Fintype.card K) n f₁)
    (hu₀ : ∀ r, f₀.eval (α r) = u₀ r) (hu₁ : ∀ r, f₁.eval (α r) = u₁ r)
    (a₀ : Polynomial L)
    (hdeg : a₀.natDegree ≤ sigma (Fintype.card K) e - 1)
    (Pz : L → Polynomial L)
    (hPz : DecodedFamily K α u₀ u₁ k e (goodParameters K α k e u₀ u₁) Pz)
    (pt : Fin k → Polynomial L)
    (hpt : ∀ j, (pt j).natDegree ≤ clearingBound (Fintype.card K) k e)
    (hspec : ∀ z ∈ regularParameters (goodParameters K α k e u₀ u₁) a₀,
      specialize (Fintype.card K) pt z =
        Polynomial.C (a₀.eval z ^ (sigma (Fintype.card K) (k - 1))) * Pz z)
    (hlarge : sigma (Fintype.card K) e * clearingBound (Fintype.card K) k e <
      (regularParameters (goodParameters K α k e u₀ u₁) a₀).card) :
    ∃ E : Submodule K L, E ≤ Submodule.span K (Set.range α) ∧ Module.finrank K E = n - e ∧
      ∀ x ∈ E, familyEval (Fintype.card K) pt x =
        a₀ ^ (sigma (Fintype.card K) (k - 1)) *
          (Polynomial.C (f₀.eval x) + Polynomial.X * Polynomial.C (f₁.eval x)) := by sorry

end GabidulinProx.UniqueDecoding
