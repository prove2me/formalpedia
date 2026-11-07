-- Prove2me | Theorems.Thm_NCPComm_corollary_4_8
-- name    : NCPComm.corollary_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:20.724745+00:00
-- url     : https://prove2.me/theorems/d1f7e98f-478b-48e6-b508-a360ee3e0343
-- title:
--   Corollary 4.8 — every interactive proof for NCP communicates $\Omega(N/K)$ bits
-- statement:
--   There are absolute constants $C_1,c_0>0$ with the following property. Let $N=3n$, and let $K=K(n)$ and $s=s(n)$ satisfy, for all large $n$, $\sqrt N<K<N$, $3K<N$ and $s\ge C_1\sqrt N$, with
--   $$
--   s=o\big(\min\{K,N/\sqrt K\}\big).
--   $$
--   Let $(V,P)$ be interactive proofs for $\mathrm{NCP}(2N,2K)$ with verifier sample count $\mathrm{Poi}(s)$ and completeness and soundness errors at most $\frac13$, against every prover strategy, with no bound on the verifier's running time and with secret verifier coins. Then, for all large $n$, the communication satisfies
--   $$
--   c(2N,2K)\ge c_0\,\frac NK.
--   $$
--
--   This is eq. (1), p.20: $c_{\mathrm{NCP}}(N,K)=\Omega(N/K)$. Since both families have $\|D\|_2^2=\Theta(1/K)$, the bound is $\Omega(N\|D\|_2^2)$, and it is what gives the paper's communication lower bounds for entropy, uniformity, support size, identity and monotonicity.
--
--   **Formalization Note** The hypotheses are about the protocol's own Poisson mean, and the protocol runs on $[2N]$ with heavy count $2K$.
--
--   Differences from the source:
--   - encoding: s ≥ C₁√N and s = o(min{K, N/√K}) on the mean after a fixed amplification → both on the protocol's own mean s(n); reason: the two means differ by an absolute odd factor t (Claim 3.10); o(·) ignores it, and C₁ is existential, so C₁/t is the constant here
--   - reading: "c(2N, 2K) = Ω(N/K)" → c₀ absolute, before the protocol family; the threshold on n depends on the family; reason: the stronger of the two readings of Ω, and the one the proof gives: c₀ comes from Razborov's constant, t and k_a/g → N/(8K)
--   - generalization: hypotheses for all N, with K = N^k → hypotheses only for large n, with no fixed k; reason: weaker hypotheses, and the page's case is a special case
--   - generalization: a prover with sample access to D (Definition 3.4) → a strategy chosen after D: a PMF over deterministic strategies for completeness, any deterministic strategy for soundness; reason: more protocols pass completeness; soundness is equivalent on the finite family, since a sample-access prover can draw more samples and identify D with error tending to 0, and the proof's own cheating prover (the YES prover for D₀(Supp(p_heavy))) is of this form
--   - generalization: a probabilistic polynomial-time verifier making adaptive sample requests → an unbounded verifier holding the Poisson pool up front, with a PMF over behaviours chosen from the sample; reason: adaptive requests are served from the pool (Claim 3.8); a lower bound over all verifiers implies the one over efficient ones
--   - encoding: communication: total bits exchanged, worst case → the depth of a bit tree with a speaker function; reason: any protocol of worst-case communication at most c is one after padding, the convention of the published DistVerif protocol
--   - encoding: labels in [N] = {1,…,N} → Fin N, 0-based; reason: Lean convention; same objects
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Corollary 4.8, concluding paragraph, p.22; eq. (1), p.20

import Mathlib
import Definitions.Def_NCPComm_setupProcedure
import Definitions.Def_NCPComm_IPProtocol

open scoped NNReal ENNReal Topology
open Filter

namespace NCPComm

/-- **Corollary 4.8 (Lower bound for NCP), concluding form, p.22, and eq. (1), p.20** (Herman, The
Communication Complexity of Verifying Distribution Properties, STOC 2027 submission, manuscript
sha256 714c0353…): every interactive proof for `NCP(2N, 2K)` with verifier sample count `Poi(s)` and
both errors at most `1/3`, where `√N < K < N`, `3K < N`, `s ≥ C₁√N` and `s = o(min{K, N/√K})`, has
communication `c(2N, 2K) = Ω(N/K)`.

**Formalization Note** Source parameters are `N = 3n` and `K(n)`, and the protocol lives on `[2N]`
with heavy count `2K`. The constants `C₁` and `c₀` are absolute and are quantified before the protocol
family. The hypotheses are on the protocol's own Poisson mean: the page puts them on the mean after a
fixed amplification, which differs by a constant factor, and `C₁` is existential. All hypotheses are
required only for large `n`. -/
theorem corollary_4_8 :
    ∃ C₁ c₀ : ℝ, 0 < C₁ ∧ 0 < c₀ ∧
      ∀ (K : ℕ → ℕ) (s : ℕ → ℝ≥0) (P : ∀ n : ℕ, IPProtocol (2 * (3 * n))),
        (∀ᶠ n : ℕ in atTop,
          Real.sqrt (3 * n) < K n ∧ (K n : ℝ) < 3 * n ∧ 3 * K n < 3 * n) →
        (∀ᶠ n : ℕ in atTop, C₁ * Real.sqrt (3 * n) ≤ (s n : ℝ)) →
        Tendsto (fun n : ℕ => (s n : ℝ) / min (K n : ℝ) (3 * n / Real.sqrt (K n))) atTop (𝓝 0) →
        (∀ᶠ n in atTop, IsNCPProof (P n) (2 * K n) (s n) (1 / 3)) →
        ∀ᶠ n : ℕ in atTop, c₀ * ((3 * n : ℝ) / K n) ≤ ((P n).depth : ℝ) := by sorry

end NCPComm
