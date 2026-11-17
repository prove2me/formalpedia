-- Prove2me | Theorems.Thm_NondetConn_Supplement_theorem_7_1
-- name    : NondetConn.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:13:10.114205+00:00
-- url     : https://prove2.me/theorems/f6ab2f62-5ee0-42d5-9d1d-ab7cf36ad233
-- title:
--   Theorem 7.1 — tight lower bound for $\mathsf{IP\circ PC}_{n,r}$ when $r=o(\log n)$
-- statement:
--   For every fixed $\varepsilon\in(0,1/2)$, there is $c>0$ with the following property. For every positive $r:\mathbb N\to\mathbb N$ satisfying $r(n)=o(\log_2 n)$ there is $n_0$ such that, for every $n\ge n_0$, every Alice-first randomized protocol for $\mathsf{IP\circ PC}_{n,r(n)}$ with at most $r(n)$ rounds and worst-case error at most $\varepsilon$ communicates at least
--   $$
--   cn\log_2n
--   $$
--   bits in the worst case.
--
--   The lower bound loses no factor depending on the number of rounds throughout this regime.
--
--   Differences from the source:
--   - reading: $r=o(\log n)$ and $R^{(r)}(\mathsf{IP\circ PC}_{n,r})=\Omega(n\log n)$ → for each fixed error, one positive constant before every integer-valued round family with $r(n)/\log_2n\to0$, followed by a family-dependent threshold; reason: this retains the varying-round asymptotic theorem rather than a fixed-round special case
--   - encoding: $[n]=\{1,\ldots,n\}$ and permutation-matrix action → `Fin n` and $(\sigma x)_j=x_{\sigma^{-1}(j)}$; reason: zero-based indexing is a bijective encoding and the inverse-index action is exactly the paper's permutation matrix convention
--   - generalization: each party receives only its owned permutation layers → each party structure also contains ignored padding at unowned layers; reason: fixing the padding recovers every source instance, while the Lean theorem covers all redundant representations because the function ignores those entries
--   - encoding: an $r$-round randomized protocol with receiver-only output → a finite communication tree with at most $r(n)$ alternating sender blocks, receiver-only correctness, and both outputs checked only when no message is sent; reason: this represents the same interactive protocols and resolves the source's undefined zero-message receiver without affecting the eventual lower bound
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), Theorem 7.1, pp.22 and 26 (PDF pp.24 and 28)

import Definitions.Def_NondetConn_Supplement_communicationRounds
import Definitions.Def_NondetConn_Supplement_ippc
import Definitions.Def_NondetConn_Supplement_solves
import Definitions.Def_NondetConn_Supplement_startsWith

set_option autoImplicit false

namespace NondetConn.Supplement

open Filter CommThresholdPR.StrongConverse

/-- **Theorem 7.1** (Zhang, *Settling Nondeterministic Communication Complexity of Graph
Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), printed pp.22 and 26,
PDF pp.24 and 28). If `r(n)=o(log₂ n)`, every `r(n)`-round randomized protocol for
`IP∘PC_{n,r(n)}` with any fixed error below `1/2` communicates `Ω(n log₂ n)` bits.

**Formalization Note** Alice's input structure supplies the odd-numbered permutation layers;
Bob's supplies `X,Y` and the even-numbered layers. Unused parity entries are ignored padding.
Fixing that padding recovers every source instance, while the statement covers all redundant
representations. The lower-bound constant is fixed across the full varying-round asymptotic
regime. -/
theorem theorem_7_1 :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ c : ℝ, 0 < c ∧ ∀ rounds : ℕ → ℕ,
      Tendsto (fun n ↦ (rounds n : ℝ) / Real.logb 2 n) atTop (nhds 0) →
      (∀ n, 1 ≤ rounds n) →
      ∃ n₀ : ℕ, ∀ n, 1 ≤ n → n₀ ≤ n →
      ∀ P : Protocol (IPPCAliceInput n (rounds n)) (IPPCBobInput n (rounds n)) Bool Bool,
        startsWith P true →
        (∀ a b ω z, P.publicLaw ω ≠ 0 → (P.tree ω).finiteRun a b z ≠ 0 →
          communicationRounds (P.tree ω) (P.bits ⟨ω, z.1⟩) ≤ rounds n) →
        solves P (fun _ _ ↦ True) (ippc n (rounds n)) ε →
        c * (n : ℝ) * Real.logb 2 n ≤ (P.cost : ℝ) := by sorry

end NondetConn.Supplement
