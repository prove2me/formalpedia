-- Prove2me | Theorems.Thm_FuzzyExtractors_LowerBound_lemma_C_1
-- name    : FuzzyExtractors.LowerBound.lemma_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:39.477626+00:00
-- url     : https://prove2.me/theorems/30b656a8-f951-4419-9f89-e39976d76e68
-- title:
--   Lemma C.1 — an (𝓜, m, m′, t) secure sketch has m′ ≤ L(𝓜, t, m)
-- statement:
--   Let $\mathcal M$ be a finite metric space with integer-valued distance $\mathrm{dis}$, and let $m, m'$ be real numbers such that $2^m = N$ is a natural number with $N\le|\mathcal M|$. If $(\mathsf{SS},\mathsf{Rec})$ is an $(\mathcal M,m,m',t)$-secure sketch, then
--   $$m' \le L(\mathcal M,t,m) = \log\Big(\min_{S\subseteq\mathcal M,\ |S|=2^m} K(\mathcal M,t,S)\Big),$$
--   where $K(\mathcal M,t,S)$ is the largest size of an $(\mathcal M,K,t)$-code all of whose points lie in $S$.
--
--   The lemma is the coding lower bound on the entropy loss of secure sketches: no sketch correcting $t$ errors can leave more residual min-entropy than the logarithm of the size of a $t$-error-correcting code fitting inside every set of $2^m$ points. It shows that the paper's Hamming and set-difference constructions are optimal for uniform inputs.
--
--   **Formalization Note** The paper leaves implicit that $L(\mathcal M,t,m)$ is defined only when $2^m$ is an integer at most $|\mathcal M|$; we state the lemma for $N\in\mathbb N$ with $N=2^m$ and $N\le|\mathcal M|$. All metric axioms of §2.1 are stated explicitly. The sketch is the worst-case secure sketch of Definition 3 (not the average-case one), with a randomized $\mathsf{Rec}$ and an arbitrary sketch output type. Efficiency is not formalized.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, Lemma C.1, p. 40

import Mathlib
import Definitions.Def_FuzzyExtractors_LowerBound_Basic

namespace FuzzyExtractors.LowerBound

/-- Lemma C.1 (Appendix C, p. 40): the existence of an (𝓜, m, m', t)-secure sketch implies
`m' ≤ L(𝓜, t, m)`, where `2^m = N` is a natural number with `N ≤ |𝓜|`. -/
theorem lemma_C_1 {M V : Type} [Fintype M] (dis : M → M → ℕ)
    (hzero : ∀ x y, dis x y = 0 ↔ x = y)
    (hsymm : ∀ x y, dis x y = dis y x)
    (htri : ∀ x y z, dis x z ≤ dis x y + dis y z)
    (m m' : ℝ) (t : ℕ)
    (SS : M → PMF V) (Rec : M → V → PMF M) (hSS : FuzzyExtractors.Hamming.IsSecureSketch dis m m' t SS Rec)
    (N : ℕ) (hN : N ≤ Fintype.card M) (hNm : (N : ℝ) = (2 : ℝ) ^ m) :
    m' ≤ L dis t N hN := by sorry

end FuzzyExtractors.LowerBound
