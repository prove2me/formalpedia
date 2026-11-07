-- Prove2me | Theorems.Thm_NCPComm_corollary_4_8_reduction
-- name    : NCPComm.corollary_4_8_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:03:50.151701+00:00
-- url     : https://prove2.me/theorems/c43c5795-d7d6-45c4-8955-2865cd061130
-- title:
--   Corollary 4.8 — the reduction clause: exact gap disjointness via an NCP proof
-- statement:
--   Let $(V,P)(N,K)$ be an interactive proof for $\mathrm{NCP}(N,K)$ with communication $c(N,K)$, verifier sample count $\mathrm{Poi}(s(N,K))$ and both errors at most $\frac13$. Let $s$ be the actual Poisson mean of the protocol at $(2N,2K)$ after a fixed constant amplification to both errors at most $0.01$. If $\log_N K\in(0.5,1)$, $s\ge C_1\sqrt N$ and $s=o(\min\{K,N/\sqrt K\})$, then exact $\mathrm{GapDisj}_{N,g,k_a,k_b}$, with $k_a=\lfloor\frac{s^2}{64K}e^{-s/(4K)}\rfloor$, $k_b=N-K$ and $g=g(N,K,s)$, can be solved with error at most $\frac13$ and communication $O(c(2N,2K))$, for all sufficiently large $N$.
--
--   **Formalization Note** The amplification is by any odd $t$ with $\exp(-2t(\frac12-\frac13)^2)\le0.01$ (for example $t=83$), and $s=t\,s_0$, where $s_0$ is the protocol's own mean (Claim 3.10). $O(c(2N,2K))$ is the explicit bound $t\cdot c(2N,2K)$.
--
--   Differences from the source:
--   - reading: "they must output 1 (accept)" (Definition 3.13), with "Alice's decision" on p.10 → only Alice's output must be correct; reason: stronger for a lower bound: a protocol where both are correct is one where Alice is; the page takes Alice's decision on p.10
--   - encoding: "a fixed constant amplification to both errors at most 0.01" → every odd t with exp(−2t(1/2−1/3)²) ≤ 0.01, with mean t·s₀; reason: Claim 3.10 gives exactly this; every such t is a fixed constant
--   - encoding: O(c(2N, 2K)) → k ≤ t·c(2N, 2K); reason: the proof runs the amplified protocol; this is an explicit bound of the stated form
--   - generalization: log_N K ∈ (0.5, 1) and the other hypotheses for all N → √N < K < N, 3K < N, and the mean conditions, for all large n; reason: weaker hypotheses than for all N; the page's case is a special case
--   - generalization: a verifier and a prover with sample access (Definition 3.4), the verifier probabilistic polynomial time → the model of IPProtocol: pool up front, unbounded verifier, prover chosen after D; reason: see the definition's note; every sample-access protocol is an instance after identification of D on the finite family, as argued for the goal
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Corollary 4.8, p.22

import Mathlib
import Definitions.Def_NCPComm_setupProcedure
import Definitions.Def_NCPComm_IPProtocol

open scoped NNReal ENNReal Topology
open Filter

namespace NCPComm

/-- **Corollary 4.8, the reduction clause, p.22** (Herman, The Communication Complexity of Verifying
Distribution Properties, STOC 2027 submission, manuscript sha256 714c0353…). Let `P` be interactive
proofs for `NCP(2N, 2K)` with `N = 3n`, Poisson mean `s₀(n)` and both errors at most `1/3`. Let
`s = t·s₀` be the Poisson mean after a fixed amplification by an odd `t` to both errors at most `0.01`
(Claim 3.10). If `s` is in the regime of Proposition 4.7, then for all sufficiently large `N`, exact
`GapDisj_{N,g,k_a,N-K}` with `k_a = ⌊(s²/(64K)) e^{-s/(4K)}⌋` and `g = g(N, K, s)` can be solved with
error at most `1/3` and communication at most `t·c(2N, 2K)`.

**Formalization Note** "A fixed constant amplification to both errors at most `0.01`" is every odd
`t` with `exp(-2t(1/2-1/3)²) ≤ 0.01`, for example `t = 83`. `C₁` is quantified before `t`, because it
comes from Proposition 4.7. `O(c(2N, 2K))` is the explicit bound `t·c(2N, 2K)`. -/
theorem corollary_4_8_reduction :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (t : ℕ), Odd t →
      Real.exp (-2 * (t : ℝ) * (1 / 2 - 1 / 3) ^ 2) ≤ 0.01 →
      ∀ (K : ℕ → ℕ) (s₀ : ℕ → ℝ≥0) (P : ∀ n : ℕ, IPProtocol (2 * (3 * n))),
        InRegime C₁ K (fun n => (t : ℝ≥0) * s₀ n) →
        (∀ᶠ n in atTop, IsNCPProof (P n) (2 * K n) (s₀ n) (1 / 3)) →
        ∀ᶠ n in atTop, ∃ (Q : DistVerif.Simulation.PubProtocol (3 * n)) (k : ℕ),
          k ≤ t * (P n).depth ∧
          SolvesExactGapDisj Q k (gapG (3 * n) (K n) ((t : ℝ≥0) * s₀ n))
            (inputSizeA (K n) ((t : ℝ≥0) * s₀ n)) (3 * n - K n) (1 / 3) := by sorry

end NCPComm
