-- Prove2me | Theorems.Thm_NondetConn_Supplement_theorem_C_1
-- name    : NondetConn.Supplement.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:14:43.901046+00:00
-- url     : https://prove2.me/theorems/0d8095b1-cc47-40b9-b9a2-afe7e51e3940
-- title:
--   Theorem C.1 — $\mathsf{IP\circ PC}$ lower bound for $r=O(n^\eta)$ rounds
-- statement:
--   Fix $\eta\in(0,1)$ and an error probability $\varepsilon\in(0,1/2)$. There is $c>0$ with the following property. For every positive $r:\mathbb N\to\mathbb N$ satisfying $r(n)=O(n^\eta)$ there is $n_0$ such that, for every $n\ge n_0$, every Alice-first randomized protocol for $\mathsf{IP\circ PC}_{n,r(n)}$ with at most $r(n)$ rounds and worst-case error at most $\varepsilon$ communicates at least
--   $$
--   cn\log_2n
--   $$
--   bits in the worst case. The hidden lower-bound constant may depend on $\eta$ but not on $n$.
--
--   This extends Theorem 7.1 from sublogarithmically many rounds to polynomially many rounds below exponent one.
--
--   Differences from the source:
--   - reading: $r=O(n^\eta)$ and $R^{(r)}(\mathsf{IP\circ PC}_{n,r})=\Omega_\eta(n\log n)$ → an explicit positive lower-bound constant chosen before every round family, then an explicit growth constant and family-dependent threshold, all independent of the growing $n$; reason: this is the quantified meaning of both asymptotic symbols and permits the lower-bound constant to depend on fixed $\eta$
--   - encoding: $[n]$ and permutation-matrix action → `Fin n` and inverse-index action on bit vectors; reason: zero-based indexing is bijective and the action is exactly the paper's permutation matrix convention
--   - generalization: each party receives only its owned permutation layers → each party structure also contains ignored padding at unowned layers; reason: fixing the padding recovers every source instance, while the Lean theorem covers all redundant representations because the function ignores those entries
--   - encoding: an $r$-round randomized protocol with receiver-only output → a finite communication tree with at most $r(n)$ alternating sender blocks, receiver-only correctness, and both outputs checked only when no message is sent; reason: this represents the same interactive protocols and resolves the source's undefined zero-message receiver without affecting the eventual lower bound
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), Theorem C.1, p.49 (PDF p.51)

import Definitions.Def_NondetConn_Supplement_communicationRounds
import Definitions.Def_NondetConn_Supplement_ippc
import Definitions.Def_NondetConn_Supplement_solves
import Definitions.Def_NondetConn_Supplement_startsWith

set_option autoImplicit false

namespace NondetConn.Supplement

open CommThresholdPR.StrongConverse

/-- **Theorem C.1** (Zhang, *Settling Nondeterministic Communication Complexity of Graph
Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), Appendix C,
printed p.49, PDF p.51). For fixed `η∈(0,1)` and a positive integer round function
`r(n)=O(n^η)`, every `r(n)`-round randomized protocol for `IP∘PC_{n,r(n)}` with fixed
error below `1/2` communicates `Ω_η(n log₂ n)` bits.

**Formalization Note** The round-growth big-O and communication lower-bound omega are each
expanded into positive constants and thresholds. The lower-bound constant is chosen before
the round family (and may depend on fixed `η` and fixed error); only the eventual threshold may
depend on the family. No constant depends on the growing `n`. Unowned-layer entries are ignored
padding; fixing them recovers every source instance, while Lean covers all redundant
representations. -/
theorem theorem_C_1 :
    ∀ η : ℝ, 0 < η → η < 1 →
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ c : ℝ, 0 < c ∧ ∀ rounds : ℕ → ℕ, (∀ n, 1 ≤ rounds n) →
      (∃ K : ℝ, 0 < K ∧ ∃ nᵣ : ℕ, ∀ n, nᵣ ≤ n →
        (rounds n : ℝ) ≤ K * (n : ℝ) ^ η) →
      ∃ n₀ : ℕ, ∀ n, 1 ≤ n → n₀ ≤ n →
      ∀ P : Protocol (IPPCAliceInput n (rounds n)) (IPPCBobInput n (rounds n)) Bool Bool,
        startsWith P true →
        (∀ a b ω z, P.publicLaw ω ≠ 0 → (P.tree ω).finiteRun a b z ≠ 0 →
          communicationRounds (P.tree ω) (P.bits ⟨ω, z.1⟩) ≤ rounds n) →
        solves P (fun _ _ ↦ True) (ippc n (rounds n)) ε →
        c * (n : ℝ) * Real.logb 2 n ≤ (P.cost : ℝ) := by sorry

end NondetConn.Supplement
