-- Prove2me | Theorems.Thm_HypRecov_Supplement_theorem_A_4
-- name    : HypRecov.Supplement.theorem_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:30:14.133207+00:00
-- url     : https://prove2.me/theorems/7d7c5884-9bec-4bff-94ef-db3c2a6c6c00
-- title:
--   Theorem A.4 — simultaneous deterministic sampled-boundary recovery
-- statement:
--   Fix a finite family $\mathcal R$ of vertex subsets and write $N_{\mathcal R}=\sum_{R\in\mathcal R}|R|$. For every simple unweighted terminal hypergraph, deterministic per-vertex linear measurements at order
--   $$q=\min\{r,\lfloor\log_2K\rfloor+3\}$$
--   recover
--   $$D_{R,S}=\{e\in E:e\cap S\ne\varnothing,\ e\cap(R\setminus S)\ne\varnothing\}$$
--   with complete original memberships for every $R\in\mathcal R$ and $S\subseteq R$ satisfying $|D_{R,S}|\le K$.
--
--   The guarantee is simultaneous, including adaptively chosen queries. State and decoder workspace use $\widetilde O(N_{\mathcal R}Kr+Kr)$ bits; per-fragment updates and per-query decoding are polynomial in $n,r,K$. Only the terminal projection vector is promised.
--
--   Differences from the source:
--   - reading: “vertex subsets $\mathcal R\subseteq[n]$” followed by $N_{\mathcal R}=\sum_{R\in\mathcal R}|R|$ → a finite family `Finset (Finset (Fin n))`; reason: this is the unique type-correct reading of the displayed sum and the later quantification over $R\in\mathcal R$
--   - encoding: deterministic per-vertex linear measurements, simultaneous adaptive queries and $\widetilde O$ resources → a state concatenating one block per vertex occurrence, depending only on the terminal vector, with uniform additive/subtraction/query TM2 machines and explicit all-stack budgets; reason: determinism makes the all-query guarantee adaptive, and the machine interface preserves every stated resource
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem A.4, p.32 (PDF p.33)

import Mathlib
import Definitions.Def_HypRecov_Supplement_QuerySketchGuarantee

set_option autoImplicit false

namespace HypRecov.Supplement

/-- **Theorem A.4 (Deterministic sparse boundary recovery).** Zhang, Chen, Shen, *Hypergraph Recovery
from Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Theorem A.4,
p.32 (PDF p.33).

For a finite family `family` of sampled vertex sets, one deterministic per-vertex additive state at
order `min{r,floor(log₂ K)+3}` recovers `D_{R,S}` with every original membership whenever
`R` belongs to the family, `S ⊆ R`, and the sampled boundary has at most `K` edges.  The same state
answers every such query, including adaptive queries.  State and decoder workspace are
`O-tilde(N_family K r + K r)`, and updates and queries are uniformly polynomial.

**Formalization Note.** The source's printed `R ⊆ [n]` followed by a sum over `R in R` is read as
the unique type-correct object: a finite family of vertex subsets.  The state depends only on the
terminal projection vector, so no prefix promise is introduced. -/
theorem theorem_A_4 :
    ∃ (A : QuerySketch) (C c : ℕ),
      ∀ (n r K : ℕ) (family : Finset (Finset (Fin n))),
        r ≤ n → 1 ≤ r → 1 ≤ K →
        let q := min r (Nat.log 2 K + 3)
        QuerySketchGuarantee A C c n r K q (familySize family * K * r + K * r) family
          (fun E R S => R ∈ family ∧ S ⊆ R ∧ (sampledBoundary E R S).card ≤ K)
          (fun E R S out => FullEdgeOutput (sampledBoundary E R S) out)
    := by sorry

end HypRecov.Supplement
