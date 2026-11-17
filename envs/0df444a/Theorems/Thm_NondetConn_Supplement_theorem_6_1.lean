-- Prove2me | Theorems.Thm_NondetConn_Supplement_theorem_6_1
-- name    : NondetConn.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:11:27.564513+00:00
-- url     : https://prove2.me/theorems/9c9bf525-0c2f-45f1-91c2-f6c0eeb2aa0e
-- title:
--   Theorem 6.1 — round-dependent randomized lower bound for $\mathsf{bConn}_N$
-- statement:
--   For every fixed error probability $\varepsilon\in(0,1/2)$, there is $c>0$ with the following property. For every positive $r:\mathbb N\to\mathbb N$ satisfying $r(N)=o(\log_2 N)$ there is $N_0$ such that, for every even $N\ge N_0$, every Alice-first randomized protocol for $\mathsf{bConn}_N$ using at most $r(N)$ rounds and having worst-case error at most $\varepsilon$ communicates at least
--   $$
--   c\frac{N}{r(N)}\log_2 N
--   $$
--   bits in the worst case.
--
--   The bound remains superlinear throughout the full $r=o(\log N)$ regime.
--
--   Differences from the source:
--   - reading: $r=o(\log N)$ and $R^{(r)}(\mathsf{bConn}_N)=\Omega((N/r)\log N)$ → for each fixed error, one positive lower-bound constant before every integer-valued round family with $r(N)/\log_2N\to0$, followed by a family-dependent threshold; reason: this is the non-vacuous quantified meaning of the two asymptotic symbols
--   - encoding: an $r$-round randomized protocol with constant error below $1/2$ → a communication tree whose maximal number of alternating sender blocks is at most $r(N)$, whose receiver has worst-case error at most a fixed $0<\varepsilon<1/2$, and whose two outputs are both checked only when no message is sent; reason: maximal sender blocks are the paper's messages/rounds, and the zero-message convention resolves an undefined receiver without affecting the positive asymptotic bound
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), Theorem 6.1, p.21 (PDF p.23)

import Definitions.Def_NondetConn_bConn
import Definitions.Def_NondetConn_Supplement_communicationRounds
import Definitions.Def_NondetConn_Supplement_solves
import Definitions.Def_NondetConn_Supplement_startsWith

set_option autoImplicit false

namespace NondetConn.Supplement

open Filter CommThresholdPR.StrongConverse

/-- **Theorem 6.1** (Zhang, *Settling Nondeterministic Communication Complexity of Graph
Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), printed p.21,
PDF p.23). If the positive integer-valued round bound satisfies `r(N)=o(log₂ N)`, every
`r(N)`-round randomized protocol for `bConn_N` with any fixed error below `1/2` communicates
`Ω((N/r(N)) log₂ N)` bits in the worst case.

**Formalization Note** Little-o is the displayed quotient tending to zero. A round is a
maximal consecutive block of bits sent by one party, not an individual bit. The constants
and threshold are uniform in the growing size `N` and its varying round count. -/
theorem theorem_6_1 :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ c : ℝ, 0 < c ∧ ∀ rounds : ℕ → ℕ,
      Tendsto (fun N ↦ (rounds N : ℝ) / Real.logb 2 N) atTop (nhds 0) →
      (∀ N, 1 ≤ rounds N) →
      ∃ N₀ : ℕ, ∀ N, 1 < N → Even N → N₀ ≤ N →
      ∀ P : Protocol (Equiv.Perm (Fin (N / 2))) (Equiv.Perm (Fin (N / 2))) Bool Bool,
        startsWith P true →
        (∀ a b ω z, P.publicLaw ω ≠ 0 → (P.tree ω).finiteRun a b z ≠ 0 →
          communicationRounds (P.tree ω) (P.bits ⟨ω, z.1⟩) ≤ rounds N) →
        solves P (fun _ _ ↦ True) (fun a b ↦ decide (NondetConn.bConn (N / 2) a b)) ε →
        c * ((N : ℝ) / (rounds N : ℝ)) * Real.logb 2 N ≤ (P.cost : ℝ) := by sorry

end NondetConn.Supplement
