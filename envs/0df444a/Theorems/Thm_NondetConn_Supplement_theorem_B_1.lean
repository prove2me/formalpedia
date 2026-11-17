-- Prove2me | Theorems.Thm_NondetConn_Supplement_theorem_B_1
-- name    : NondetConn.Supplement.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:14:07.631947+00:00
-- url     : https://prove2.me/theorems/ccae8111-15b8-47b5-b447-7dd3cd220caa
-- title:
--   Theorem B.1 — round-efficient deterministic permutation pointer chasing
-- statement:
--   There are an absolute constant $C>0$ and a threshold $n_0$ such that, for every $n\ge n_0$ and $r\ge1$:
--
--   1. if $k\le r^2$, then $\mathsf{PC\text{-}Perm}_{n,k}$ has an $r$-round deterministic protocol, starting with Bob, whose worst-case communication is at most $Cnr^2\log_2\log_2n$;
--   2. if $k\le r^2+r$, then $\mathsf{bPC\text{-}Perm}_{n,k}$ has such a protocol with the same bound.
--
--   Only the receiver of the final message is required to output.
--
--   Differences from the source:
--   - reading: both communication costs are $O(nr^2\log\log n)$ → one positive constant and one threshold chosen before $n,r,k$ and shared by both clauses; reason: this is the uniform, non-vacuous quantified meaning of the printed big-O, including small values where $\log\log n$ is not positive
--   - encoding: $[n]$ is one-based and $\mathsf{bPC\text{-}Perm}$ outputs the parity of $v_k$ → `Fin n` and parity of `v.val + 1`; reason: these are bijective zero-based encodings of vertices and the same output bit
--   - generalization: the source fixes the starting vertex and gives each party only its owned layers → Lean treats the starting vertex as Alice input and gives both party structures ignored padding at unowned layers; reason: fixing the starting vertex and padding recovers every source instance, while the source's delayed-start proof explicitly supports the stronger variable-start protocol
--   - encoding: deterministic $r$-round Bob-first protocol with receiver-only output → a point-mass protocol tree, Bob at the root, at most $r$ alternating sender blocks, receiver-only zero-error correctness, and both outputs checked only when no message is sent; reason: this makes every protocol convention in Appendix B explicit and resolves the undefined zero-message receiver
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), Theorem B.1, p.45 (PDF p.47)

import Definitions.Def_NondetConn_Supplement_bpcPerm
import Definitions.Def_NondetConn_Supplement_communicationRounds
import Definitions.Def_NondetConn_Supplement_isDeterministic
import Definitions.Def_NondetConn_Supplement_solves
import Definitions.Def_NondetConn_Supplement_startsWith

set_option autoImplicit false

namespace NondetConn.Supplement

open CommThresholdPR.StrongConverse

/-- **Theorem B.1** (Zhang, *Settling Nondeterministic Communication Complexity of Graph
Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), Appendix B,
printed p.45, PDF p.47). There is one eventual constant for which, for all `n,r ≥ 1`,
`PC-Perm_{n,k}` with `k ≤ r²` and `bPC-Perm_{n,k}` with `k ≤ r²+r` have deterministic
`r`-round Bob-first protocols using `O(n r² log₂ log₂ n)` bits. Only the receiver of the
last message must output.

**Formalization Note** The source's big-O is expanded into one positive constant and a size
threshold, both before `n,r,k`. Determinism means a single public coin and point-mass local
kernels inside the shared general protocol model. The source fixes the starting vertex and gives
each party only its owned layers; Lean strengthens this to the delayed variable start used in the
proof and ignored padding at unowned layers. Fixing both recovers the source problem. -/
theorem theorem_B_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → 1 ≤ n →
      ∀ r, 1 ≤ r →
      ((∀ k, k ≤ r ^ 2 →
        ∃ P : Protocol (PCPermAliceInput n k) (PCPermBobInput n k) (Fin n) (Fin n),
          isDeterministic P ∧ startsWith P false ∧
          (∀ a b ω z, P.publicLaw ω ≠ 0 → (P.tree ω).finiteRun a b z ≠ 0 →
            communicationRounds (P.tree ω) (P.bits ⟨ω, z.1⟩) ≤ r) ∧
          solves P (fun _ _ ↦ True) (pcPerm n k) 0 ∧
          (P.cost : ℝ) ≤ C * n * r ^ 2 * Real.logb 2 (Real.logb 2 n)) ∧
       (∀ k, k ≤ r ^ 2 + r →
        ∃ P : Protocol (PCPermAliceInput n k) (PCPermBobInput n k) Bool Bool,
          isDeterministic P ∧ startsWith P false ∧
          (∀ a b ω z, P.publicLaw ω ≠ 0 → (P.tree ω).finiteRun a b z ≠ 0 →
            communicationRounds (P.tree ω) (P.bits ⟨ω, z.1⟩) ≤ r) ∧
          solves P (fun _ _ ↦ True) (bpcPerm n k) 0 ∧
          (P.cost : ℝ) ≤ C * n * r ^ 2 * Real.logb 2 (Real.logb 2 n))) := by sorry

end NondetConn.Supplement
