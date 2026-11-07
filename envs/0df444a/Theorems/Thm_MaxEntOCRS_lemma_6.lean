-- Prove2me | Theorems.Thm_MaxEntOCRS_lemma_6
-- name    : MaxEntOCRS.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:31:27.589234+00:00
-- url     : https://prove2.me/theorems/caaa63f9-0063-4e9b-998d-e8ccd7339bc8
-- title:
--   Lemma 6 — row-sum bound $\sum_{j\ne i}|\mathrm{Cov}(X_i,X_j)| \le p_i(1-p_i)$
-- statement:
--   Let $\nu$ be a right-half-plane zero-free probability distribution on the subsets $F$ of a finite index set, $X_i = \mathbf 1\{i\in F\}$, $p_i = \mathbb E X_i$ and $p_{ij} = \mathbb E X_iX_j$. Then for every $i$,
--   $$
--   \sum_{j \ne i} \big|\mathrm{Cov}(X_i, X_j)\big| = \sum_{j \ne i} |p_{ij} - p_i p_j| \le p_i(1 - p_i) .
--   $$
--
--   The proof of Theorem 2 uses it at the neighbour of largest normalized weight.
--
--   Differences from the source:
--   - encoding: ν a right-half-plane zero-free distribution on 2^[k] → ν : Finset ι → ℝ on a finite type ι with ν ≥ 0, Σ ν = 1 and IsRHPZeroFree ν; reason: a law is a nonnegative function of total mass 1; same objects
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Lemma 6, p.6 (proof in A.4, p.13); [AASV21, Theorem 51]

import Mathlib
import Definitions.Def_MaxEntOCRS_IsRHPZeroFree
import Definitions.Def_MaxEntOCRS_incProb
import Definitions.Def_MaxEntOCRS_pairIncProb

namespace MaxEntOCRS

/-- Lemma 6 ([AASV21, Theorem 51]; Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), p.6; A.4, p.13): if the law `ν` of a random subset
`F` of a finite index set is right-half-plane zero-free, then for every `i`,
`∑_{j ≠ i} |Cov(X_i, X_j)| ≤ p_i(1 − p_i)`, where `X_i = 1{i ∈ F}`,
`Cov(X_i, X_j) = p_ij − p_i p_j`. -/
theorem lemma_6 {ι : Type} [Fintype ι] [DecidableEq ι] (ν : Finset ι → ℝ)
    (hν0 : ∀ F, 0 ≤ ν F) (hν1 : ∑ F, ν F = 1) (hν : IsRHPZeroFree ν) (i : ι) :
    ∑ j ∈ Finset.univ.erase i, |pairIncProb ν i j - incProb ν i * incProb ν j| ≤
      incProb ν i * (1 - incProb ν i) := by sorry

end MaxEntOCRS
