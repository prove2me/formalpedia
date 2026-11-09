-- Prove2me | Theorems.Thm_IntADSat_theorem_S1_1
-- name    : IntADSat.theorem_S1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:52:04.050585+00:00
-- url     : https://prove2.me/theorems/15d6fa3f-99b2-4cd9-a636-47de5ae305b0
-- title:
--   Theorem S1.1 — saturation at the prime two
-- statement:
--   Let $G\sim G(n,1/2)$ and $M_2(G)=\mathbb F_2\langle A,D\rangle e$, with $A,D$ reduced modulo $2$. For every $n\ge48$,
--
--   $$
--   \Pr\big[M_2(G)\neq\mathbb F_2^n\big]\le 4\exp(-n/18)+1024(n+1)^4\,2^{-n/48}.\qquad\text{(S1.1)}
--   $$
--
--   Consequently $M_2(G)=\mathbb F_2^n$ with probability $1-\exp(-\Omega(n))$.
--
--   The prime $2$ is special: adjacency powers alone never generate $\mathbb F_2^n$ for $n>1$, and the degree-parity operator removes this obstruction.
--
--   Differences from the source:
--   - reading: with probability 1 − exp(−Ω(n)) → ∃ c > 0, eventually failure probability ≤ exp(−cn); reason: the meaning of exp(−Ω(n))
--   - encoding: G ∼ G(n, 1/2) on the labelled vertex set [n] → erProb n (1/2) on SimpleGraph (Fin n) (published Erdős–Rényi product weight at edge probability 1/2); reason: same law: every labelled graph has probability 2^(−n(n−1)/2)
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Theorem S1.1, p.23 (PDF 24)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_IntADSat_wordModule

set_option autoImplicit false

namespace IntADSat

/-- **Theorem S1.1** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.23 (PDF 24)). Let `G ∼ G(n, 1/2)`. For every `n ≥ 48`,
`Pr[M₂(G) ≠ 𝔽₂ⁿ] ≤ 4 exp(−n/18) + 1024(n + 1)⁴ 2^{−n/48}` (S1.1). Consequently `M₂(G) = 𝔽₂ⁿ` with
probability `1 − exp(−Ω(n))`.

**Formalization Note** `1 − exp(−Ω(n))` is read as: there is `c > 0` with failure probability at most
`exp(−cn)` for all large `n`. -/
theorem theorem_S1_1 :
    (∀ n : ℕ, 48 ≤ n → LPCommunity.SBMRecovery.erProb n (1 / 2) (fun G => wordModule (ZMod 2) G ≠ ⊤) ≤
      4 * Real.exp (-(n : ℝ) / 18) + 1024 * ((n : ℝ) + 1) ^ 4 * (2 : ℝ) ^ (-(n : ℝ) / 48)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      LPCommunity.SBMRecovery.erProb n (1 / 2) (fun G => wordModule (ZMod 2) G ≠ ⊤) ≤ Real.exp (-c * n)) := by sorry

end IntADSat
