-- Prove2me | Theorems.Thm_HypRecov_Supplement_theorem_A_6
-- name    : HypRecov.Supplement.theorem_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:31:15.751105+00:00
-- url     : https://prove2.me/theorems/6e3b1b33-7b57-4458-a0ec-486eea627fba
-- title:
--   Theorem A.6 — exact-order recovery on every certified full cut
-- statement:
--   Let $k\ge2$, $K=k-1$, and $d=\lceil\log_2k\rceil$. A deterministic one-pass sketch at order
--   $$q=\min\{r,d+1\}$$
--   uses $\widetilde O(nrk)$ bits and, for every supplied $S\subseteq V$ with $|\delta_H(S)|<k$, recovers the entire boundary with complete original memberships in polynomial time. The same state answers every such cut, including adaptively chosen queries.
--
--   If $n\ge2r$, this order is exactly the least observation order that determines memberships of all $k$-crisp edges.
--
--   Differences from the source:
--   - encoding: a supplied full-vertex cut $S\subseteq V$ → the generic sampled-boundary query `(R,S)` with `R=univ`; reason: then $D_{R,S}=\delta_H(S)$ definitionally, with no change of instances
--   - encoding: deterministic one-pass sketch, adaptive queries and $\widetilde O(nrk)$ resources → one per-vertex terminal-state function and uniform additive/subtraction/query TM2 machines with absolute constants and all-stack bounds; reason: this is the machine-level reading of the same state, simultaneity and resources
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem A.6, pp.33-34 (PDF pp.34-35)

import Mathlib
import Definitions.Def_HypRecov_qid
import Definitions.Def_HypRecov_Supplement_QuerySketchGuarantee

set_option autoImplicit false

namespace HypRecov.Supplement

/-- **Theorem A.6 (Recovery at the exact order on certified full cuts).** Zhang, Chen, Shen,
*Hypergraph Recovery from Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256
719dcfff…), Theorem A.6, pp.33–34 (PDF pp.34–35).

For `k ≥ 2`, one deterministic one-pass per-vertex additive state at order
`min{r,1+ceil(log₂ k)}` uses `O-tilde(nrk)` bits and recovers the complete original boundary of
every supplied full-vertex cut of value below `k`.  One state answers all such cuts, including
adaptive queries, in uniform polynomial time.  When `n ≥ 2r`, this is exactly the least order that
determines memberships of `k`-crisp edges.

**Formalization Note.** A full cut is passed through the generic query interface as `(R,S)` with
`R=univ`.  Determinism plus a state depending only on the terminal projection gives the simultaneous
adaptive guarantee. -/
theorem theorem_A_6 :
    ∃ (A : QuerySketch) (C c : ℕ),
      ∀ (n r k : ℕ), r ≤ n → 1 ≤ r → 2 ≤ k →
        QuerySketchGuarantee A C c n r (k - 1) (HypRecov.qid r k) (n * r * k)
          ({Finset.univ} : Finset (Finset (Fin n)))
          (fun E R S => R = Finset.univ ∧ S ⊆ R ∧ HypRecov.cut E S < k)
          (fun E _ S out => FullEdgeOutput (HypRecov.bdry E S) out) ∧
        (2 * r ≤ n →
          IsLeast {q : ℕ | 1 ≤ q ∧ q ≤ r ∧ DeterminesCrisp n r k q} (HypRecov.qid r k))
    := by sorry

end HypRecov.Supplement
