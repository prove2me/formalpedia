-- Prove2me | Theorems.Thm_OWMR_canonical_width_bound
-- name    : OWMR.canonical_width_bound
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T01:37:56.631472+00:00
-- url     : https://prove2.me/theorems/66d60842-a17a-46bf-b4bb-0429a0d63c97
-- title:
--   Canonical width bound: $\beta\hat w\le\frac{h(H_i+p)}{H_i(h+p)}J_i(k)$
-- statement:
--   This is the canonical width bound in Step 2 of the proof of Lemma 3, which is also the first inequality of (31).
--
--   Consider an OWMR network that satisfies the standing assumptions, a retailer $i$, and a setup cost $k$. Let $(\hat s,\hat S)$ be a canonical optimum of retailer $i$'s single-location problem at setup cost $k$: $\hat s<\hat S$, the $(\hat s,\hat S)$ policy attains $G=J_i(k)$, $F_i(\hat s)=G$, and $F_i\le G$ on $[\hat s,\hat S]$. Then, with $\beta=hp/(h+p)$ and the width $\hat w=\hat S-\hat s$,
--
--   $$\beta\hat w\le\frac{h(H_i+p)}{H_i(h+p)}\,J_i(k).$$
--
--   When $H_i\ge h$ the coefficient is at most $1$, which gives the bound $\beta\hat w\le G$ of Lemma 3; when $H_i\ge mh$ and $p\ge h$ it is at most $(m+1)/(2m)$, as used in (31).
--
--   **Formalization Note** The canonical optimum is `IsCanonicalOptimum`; the coefficient enters through `ENNReal.ofReal`.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Lemma 3 (Canonical Savings and Width), Step 2 of its proof, pp. 14-15, and the first inequality of eq. (31) in Section 5.4, p. 26.

import Definitions.Def_owmr_single_location

open scoped ENNReal

namespace OWMR
theorem canonical_width_bound {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n)
    (k sh Sh : ℝ) (hcan : IsCanonicalOptimum (N.marginal i) (N.F i) k sh Sh) :
    ENNReal.ofReal (N.h * N.p / (N.h + N.p) * (Sh - sh))
      ≤ ENNReal.ofReal (N.h * (N.H i + N.p) / (N.H i * (N.h + N.p))) * N.J i k := by sorry
end OWMR
