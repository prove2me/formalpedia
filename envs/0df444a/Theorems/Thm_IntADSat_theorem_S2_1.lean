-- Prove2me | Theorems.Thm_IntADSat_theorem_S2_1
-- name    : IntADSat.theorem_S2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:52:21.736259+00:00
-- url     : https://prove2.me/theorems/5b34844a-9983-43c3-8039-1799c83e6263
-- title:
--   Theorem S2.1 — fixed odd primes
-- statement:
--   Let $p$ be a fixed odd prime and $G\sim G(n,1/2)$, with $A$ and $D=\operatorname{diag}(Ae)$ reduced modulo $p$. There are constants $c_p,K_p>0$ such that, for every $n\ge1$,
--
--   $$
--   \Pr\big[A,D\text{ have a nonzero proper common invariant subspace of }\mathbb F_p^n\big]\le\frac{K_p}n+K_p\exp(-c_pn).
--   $$
--
--   Consequently $\mathbb F_p\langle A,D\rangle e=\mathbb F_p^n$ with probability tending to one.
--
--   Differences from the source:
--   - reading: constants c_p, K_p > 0 with the bound (for all n) → ∃ c K > 0 with the bound for every n ≥ 1; reason: the proof covers the small n by enlarging K_p (p.35); n = 0 is excluded only because K/0 = 0 in Lean
--   - reading: with probability tending to one → Tendsto of Pr[M_p(G) = 𝔽_pⁿ] to 1; reason: same meaning
--   - encoding: fixed odd prime p → p prime with p ≠ 2; reason: same primes
--   - encoding: G ∼ G(n, 1/2) on the labelled vertex set [n] → erProb n (1/2) on SimpleGraph (Fin n) (published Erdős–Rényi product weight at edge probability 1/2); reason: same law: every labelled graph has probability 2^(−n(n−1)/2)
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Theorem S2.1, p.30 (PDF 31)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_IntADSat_wordModule
import Definitions.Def_IntADSat_HasProperInvariant

set_option autoImplicit false

namespace IntADSat

/-- **Theorem S2.1** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.30 (PDF 31)). For every fixed odd prime `p`, there are constants
`c_p, K_p > 0` such that `Pr[A, D have a nonzero proper common invariant subspace] ≤ K_p/n + K_p exp(−c_p n)`.
Consequently `𝔽_p⟨A, D⟩e = 𝔽_pⁿ` with probability tending to one.

**Formalization Note** The bound is stated for every `n ≥ 1` (the proof covers the small `n` by
enlarging `K_p`, p.35); `A`, `D` are reduced modulo `p`. -/
theorem theorem_S2_1 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      LPCommunity.SBMRecovery.erProb n (1 / 2) (fun G => HasProperInvariant (ZMod p) G) ≤ K / n + K * Real.exp (-c * n)) ∧
    Filter.Tendsto (fun n : ℕ => LPCommunity.SBMRecovery.erProb n (1 / 2) (fun G => wordModule (ZMod p) G = ⊤))
      Filter.atTop (nhds 1) := by sorry

end IntADSat
