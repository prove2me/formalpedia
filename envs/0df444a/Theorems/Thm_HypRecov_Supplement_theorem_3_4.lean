-- Prove2me | Theorems.Thm_HypRecov_Supplement_theorem_3_4
-- name    : HypRecov.Supplement.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:26:30.279558+00:00
-- url     : https://prove2.me/theorems/e7b1d058-8d2d-4b0d-842a-42bc1d1a52eb
-- title:
--   Theorem 3.4 — exact observation threshold $\min\{r,1+\lceil\log_2 k\rceil\}$
-- statement:
--   Let $n\ge2r$, $r\ge2$, and $k\ge2$. Among orders $q\in\{1,\ldots,r\}$, the least order whose complete multiplicity-preserving $q$-observation determines $\mathcal B_k(H)$ for every simple unweighted $r$-uniform hypergraph on the fixed vertex set $[n]$ is
--   $$q_{\mathrm{id}}(n,r,k)=\min\{r,1+\lceil\log_2 k\rceil\}.$$
--
--   Thus this order is sufficient for every input, while every smaller order admits two inputs with the same observation and different $k$-crisp edge families.
--
--   Differences from the source:
--   - encoding: $q_{\mathrm{id}}(n,r,k)$ on a fixed $n$-vertex set → `HypRecov.qid r k` and an `IsLeast` predicate over simple uniform hypergraphs on `Fin n`; reason: the displayed formula is independent of $n$, while `Fin n` fixes the common labelled vertex set and `IsLeast` retains both directions
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem 3.4, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_HypRecov_qid
import Definitions.Def_HypRecov_Supplement_IsCutDegenerate

set_option autoImplicit false

namespace HypRecov.Supplement

/-- **Theorem 3.4 (Exact observation threshold).** Zhang, Chen, Shen, *Hypergraph Recovery from
Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Theorem 3.4,
p.7 (PDF p.8).  For `n ≥ 2r`, `r ≥ 2`, and `k ≥ 2`, the least multiplicity-preserving
projection order that determines the complete family of `k`-crisp edges of every simple unweighted
`r`-uniform hypergraph on `Fin n` is `min r (1 + ceil(log₂ k))`.

**Formalization Note.** `IsLeast` records both directions: `qid r k` determines `B_k(H)`, and every
smaller order in `{1,…,r}` fails for some pair of simple `r`-uniform hypergraphs on the same fixed
vertex set. -/
theorem theorem_3_4 (n r k : ℕ) (hn : 2 * r ≤ n) (hr : 2 ≤ r) (hk : 2 ≤ k) :
    IsLeast {q : ℕ | 1 ≤ q ∧ q ≤ r ∧ DeterminesCrisp n r k q} (HypRecov.qid r k)
    := by sorry

end HypRecov.Supplement
