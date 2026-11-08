-- Prove2me | Theorems.Thm_MonoidProdQ_adv_lower_bound
-- name    : MonoidProdQ.adv_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:55:29.210329+00:00
-- url     : https://prove2.me/theorems/a0c7afaf-69aa-4c37-abe0-ccca8b32eef8
-- title:
--   Proof of Theorem 18: $\mathrm{ADV}^{\pm}(\mathrm{Prod}_{M,G,n})\ge\sqrt{r(n-r+1)}$
-- statement:
--   Let $M$ be a finite commutative aperiodic monoid, $G\subseteq M$ with $1\in G$ and $\beta_G(M)\ge1$, let $n\ge1$ and put $r=\min\{\beta_G(M),\lfloor (n+1)/2\rfloor\}$. Then
--
--   $$\mathrm{ADV}^{\pm}(\mathrm{Prod}_{M,G,n})\ \ge\ \sqrt{r(n-r+1)}.$$
--
--   In the paper the bound comes from an explicit adversary matrix: $X$ is the set of length-$n$ arrangements of the letters of a word $w$ of length $r$ without proper product-preserving subword and $n-r$ identities, $Y$ the inputs obtained by replacing one nonidentity letter by the identity, and $A$ the $(r,n-r+1)$-biregular adjacency matrix of inputs differing in one coordinate, with $\|A\|=\sqrt{r(n-r+1)}$ and every masked matrix a matching of norm at most one. Together with Eq. (2) it gives the lower bound $\Omega(\min\{n,\sqrt{n\beta_G(M)}\})$ of Theorem 18.
--
--   Differences from the source:
--   - reading: The adversary lower bound therefore gives $\Omega(\sqrt{r(n-r+1)})$ queries → $\mathrm{ADV}^{\pm}(\mathrm{Prod}_{M,G,n})\ge\sqrt{r(n-r+1)}$; reason: the page's matrix $\Gamma$ certifies this value of the adversary ratio ($\|\Gamma\|=\|A\|$, masked norms at most one); the query bound is this item combined with Eq. (2)
--   - encoding: $r=\min\{\beta_G(M),\lfloor (n+1)/2\rfloor\}$ → `(min (productBreadth G) (((n + 1) / 2 : ℕ) : ℕ∞)).toNat`, and $n-r+1$ in `ℝ`; reason: the minimum is taken in `ℕ∞` first, so it is finite and equals $\lfloor (n+1)/2\rfloor$ when $\beta_G(M)=\infty$
--   - encoding: $\mathrm{ADV}^{\pm}$ and $Q_{1/3}$ as numbers → `ADV±` in `ℝ≥0∞`, $Q_{1/3}$ in `ℕ∞` (cast to `ℝ≥0∞`); reason: Lean convention; suprema and infima are never junk values, and both are finite in every instance
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), proof of Theorem 18, p.34

import Definitions.Def_MonoidProdQ_IsAperiodic
import Definitions.Def_MonoidProdQ_productBreadth
import Definitions.Def_MonoidProdQ_prodMap
import Definitions.Def_MonoidProdQ_advPm

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), proof of Theorem 18, lower bound, p.34: for a finite commutative aperiodic monoid
`M`, `G ⊆ M` with `1 ∈ G` and `β_G(M) ≥ 1`, `n ≥ 1` and `r = min{β_G(M), ⌊(n+1)/2⌋}`, the
adversary matrix built from the `(r, n−r+1)`-biregular graph between the inputs `X` (the length-`n`
arrangements of a word without proper product-preserving subword and `n − r` identities) and
`Y` (one nonidentity letter replaced by the identity) has `‖A‖ = √(r(n−r+1))` and masked norms at
most one, so `ADV±(Prod_{M,G,n}) ≥ √(r(n−r+1))`.

**Formalization Note.** `r` is computed in `ℕ∞` and converted to a natural number (finite since
`⌊(n+1)/2⌋` is); `n − r + 1` is real subtraction (and `r ≤ n`). -/
theorem adv_lower_bound {M : Type*} [CommMonoid M] [Fintype M] [DecidableEq M]
    (hM : IsAperiodic M) (G : Finset M) (hG : (1 : M) ∈ G) (hβ : 1 ≤ productBreadth G) (n : ℕ)
    (hn : 1 ≤ n) :
    ENNReal.ofReal (Real.sqrt
        (((min (productBreadth G) (((n + 1) / 2 : ℕ) : ℕ∞)).toNat : ℝ) *
          ((n : ℝ) - ((min (productBreadth G) (((n + 1) / 2 : ℕ) : ℕ∞)).toNat : ℝ) + 1))) ≤
      advPm (prodMap G n) Finset.univ := by sorry

end MonoidProdQ
