-- Prove2me | Theorems.Thm_MixedORAM_PublicRead_theorem_3_1
-- name    : MixedORAM.PublicRead.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:50:09.775896+00:00
-- url     : https://prove2.me/theorems/dcac1865-2dd4-49a7-af68-acc60b09a1ab
-- title:
--   Theorem 3.1 — public-read lower bound R_N ≥ c·G_p(Q) under a private budget Q
-- statement:
--   Fix $\varepsilon>0$ and an address-width constant $\lambda>0$. There are $c>0$ and $n_0$, depending only on $\varepsilon$ and $\lambda$, such that the following holds for all $n\ge n_0$, $m\le n^{1-\varepsilon}$, $w\ge\lceil\log_2 n\rceil$, physical addresses of $a\le\lambda w$ bits, $0<p\le1/2$, horizons $N\ge4n/p$ and budgets $Q>0$.
--
--   Consider the workload $\mathcal W_{R,W}$ (public reads, private writes) with disclosed-kind privacy, or $\mathcal W_{R,R}$ (public and private reads) with hidden-kind privacy. Let $I$ be an online randomized cell-probe implementation with $mw$ retained client bits and $a$-bit addresses that has per-read correctness at least $2/3$ on every fixed full-API input and statistical trace privacy on horizon $N+2$ (total variation at most $1/16$ on comparable inputs). Then for every initial array, if $\Pi_N\le Q$ on the workload, or if $I$ has a worst-case-input private budget $P\le Q$,
--   $$R_N\ \ge\ c\,G_p(Q),\qquad G_p(Q)=\max\Big\{1,\frac{H}{\log_2(2+1/p+Q/H)}\Big\},\quad H=\log_2\Big(2+\frac n{m+1}\Big).$$
--
--   The same holds with computational trace privacy: for every computationally private implementation family and every polynomial parameter bound and every choice of initial arrays (one for each $\kappa$ and parameter tuple) on which the exact workload execution (preprocessing included) has polynomial expected probe count, there is $\kappa_0$ such that the bound holds on those arrays, with the same $c$, for all $\kappa\ge\kappa_0$ and all parameters within the bound that meet the assumptions above (including $n\ge n_0$) and for which $A_\kappa$ is correct. No cryptographic assumption or lower bound on $m$ is needed.
--
--   This is the lower half of the paper's public-read/private-write frontier: at constant $p$ a logarithmic private budget forces logarithmic public reads, so a passive server cannot match constant-public, logarithmic-private guarantees.
--
--   Differences from the source:
--   - encoding: an online randomized implementation whose preprocessing and requests have independent random tapes (p. 14); a request's computation may flip coins → Impl: preprocessing is a law over (its probes, initial server memory, client state) given the initial array; each request runs a cell-probe decision tree drawn from a law that depends only on the retained state and the request; reason: a randomized program with internal coins is a mixture of deterministic decision trees; the paper's WLOG independent tapes (p. 14)
--   - generalization: the client retains at most mw bits, counting all transient state → only the client state kept between requests (and left by preprocessing) is bounded, by m·w bits (BitVec (m*w)); work inside one request is free; reason: every implementation of the source is one of these, so the Lean hypothesis is weaker; the proof's encoder sends only the retained post-epoch state (p. 16)
--   - encoding: O(w)-bit physical addresses → a-bit addresses (2^a cells, BitVec a) with a ≤ λw for a fixed λ > 0, the constants depending on λ; reason: Theorem A.1 (p. 14) makes the O(w) explicit as 'at most λw bits for a fixed λ'
--   - encoding: addresses in [n]; w ≥ ⌈log2 n⌉; words of w bits → Fin n (0-based) with [NeZero n]; Nat.clog 2 n ≤ w; BitVec w; reason: Lean conventions; n ≥ 1 is needed for a uniform address and holds for n ≥ n₀ ≥ 1
--   - encoding: real average costs Π_N, R_N → Π_N, R_N in [0, ∞] (ENNReal); the bound reads ENNReal.ofReal(c·G_p(Q)) ≤ R_N; reason: an expectation of a probe count may be infinite; R_N = ∞ satisfies the bound and Π_N ≤ Q forces finiteness; no finiteness hypothesis is added
--   - encoding: trace privacy: comparable inputs (same leakage, same initial array) have traces within total variation 1/16 on horizon N + 2 → StatPrivate k I (N + 2) (1/16): for every initial array and every two full-API request lists of length ≤ N + 2 with equal leakage (Leak_dis or Leak_hid), the laws of the observed traces (preprocessing probes, then the probes of each request) are within total variation 1/16; reason: §2.2 and Appendix G; 'comparable' needs equal leakage and the same initial array
--   - encoding: the same holds under a worst-case-input budget P ≤ Q → WorstCaseBudget I Q; reason: a budget P ≤ Q is also a budget Q, and a budget Q is a budget P = Q
--   - encoding: 'every secure family' under 'the lower-bound conditions' (storage, per-read correctness, privacy, expected-probe qualification) → a statistical clause (one implementation, StatPrivate on horizon N + 2 with distance 1/16) and a computational clause (a family with CompPrivate and the expected-probe qualification), with one constant c; reason: §2.2 and Appendix G give both notions; neither implies the other
--   - encoding: nonuniform polynomial-time samplers and distinguishers; polynomial probe cutoffs; negligible advantage (Appendix G) → samplers are polynomial-size multi-output circuit families (published LaconicBarrier.MCircuit) on uniform coins whose output is a fixed injective code of (A₀, u₀, u₁, z); distinguishers are the published NoisyOWMPC.Distinguisher (polynomial-size circuits); cutoffs b(κ) ≤ (κ+2)^c; advantage negligible in the sense of the published NoisyOWMPC.Negligible; reason: circuit families are the nonuniform polynomial-time model; randomness of a nonuniform distinguisher can be fixed to its best value
--   - reading: for each fixed secure family and fixed polynomial parameter bounds, the inequality holds for all sufficiently large κ, uniformly over parameters satisfying both those bounds and the theorem's assumptions (Appendix G, p. 76) → for every family A that is computationally private, every d, every choice Arr κ P of an initial array for each κ and P, and every exponent e bounding the expected probes (preprocessing included) of the exact workload execution from Arr κ P by (κ+2)^e over the parameter range, there is κ₀ such that for all κ ≥ κ₀ and all parameters P within (κ+2)^d (n, w, m, a, N, 1/p, Q) that meet the assumptions, including n ≥ n₀, the bound holds on the initial array Arr κ P with the same constant c; reason: Theorem A.1 says the computational case 'additionally' requires its conditions on top of 'for all sufficiently large n'; the expected-probe qualification is asked uniformly over the polynomial range, as Appendix G (p. 76) says, and only of the initial arrays the conclusion is about (a bound uniform over every initial array would be the narrower reading)
--   - generalization: p is efficiently samplable; budgets have polynomial-length descriptions → no condition on how p and Q are described; reason: dropping hypotheses gives a stronger statement that specializes to the source's; a nonuniform sampler approximates any p with 1/p polynomial to within 2^{-κ} per request, and Q enters only the final algebra
-- source:
--   Ciszewski, Ragnoli, Access Cost Tradeoffs in Mixed-Mode Oblivious RAM, STOC 2027 submission (manuscript sha256 a4f849fd…), p. 6, Theorem 3.1; proof p. 35

import Mathlib
import Definitions.Def_MixedORAM_PublicRead_CompPrivacy
import Definitions.Def_MixedORAM_PublicRead_Frontier

set_option autoImplicit false

namespace MixedORAM.PublicRead

theorem theorem_3_1 (ε lam : ℝ) (hε : 0 < ε) (hlam : 0 < lam) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      (∀ (wl : Workload) (n w m a N : ℕ) [NeZero n] (p Q : ℝ),
        n₀ ≤ n → (m : ℝ) ≤ (n : ℝ) ^ (1 - ε) → Nat.clog 2 n ≤ w → (a : ℝ) ≤ lam * w →
        0 < p → p ≤ 1 / 2 → 4 * (n : ℝ) / p ≤ N → 0 < Q →
        ∀ I : Impl n w m a, I.Correct → StatPrivate wl.leak I (N + 2) (1 / 16) →
          ∀ A₀ : Fin n → BitVec w,
            (PiN I A₀ wl p N ≤ ENNReal.ofReal Q ∨ WorstCaseBudget I Q) →
              ENNReal.ofReal (c * Gp n m p Q) ≤ RN I A₀ wl p N) ∧
      (∀ (wl : Workload) (A : Family), CompPrivate wl.leak A →
        ∀ (d : ℕ) (Arr : (κ : ℕ) → (P : Params) → Fin P.n → BitVec P.w),
          (∃ e : ℕ, ∀ (κ : ℕ) (P : Params) [NeZero P.n], P.Within d κ → n₀ ≤ P.n →
            (P.m : ℝ) ≤ (P.n : ℝ) ^ (1 - ε) → Nat.clog 2 P.n ≤ P.w → (P.a : ℝ) ≤ lam * P.w →
            0 < P.p → P.p ≤ 1 / 2 → 4 * (P.n : ℝ) / P.p ≤ P.N → 0 < P.Q →
              expProbes (A κ P) (Arr κ P) wl P.p P.N ≤ ((κ + 2 : ℕ) : ENNReal) ^ e) →
          ∃ κ₀ : ℕ, ∀ κ ≥ κ₀, ∀ (P : Params) [NeZero P.n], P.Within d κ → n₀ ≤ P.n →
            (P.m : ℝ) ≤ (P.n : ℝ) ^ (1 - ε) → Nat.clog 2 P.n ≤ P.w → (P.a : ℝ) ≤ lam * P.w →
            0 < P.p → P.p ≤ 1 / 2 → 4 * (P.n : ℝ) / P.p ≤ P.N → 0 < P.Q →
            (A κ P).Correct →
              (PiN (A κ P) (Arr κ P) wl P.p P.N ≤ ENNReal.ofReal P.Q ∨
                  WorstCaseBudget (A κ P) P.Q) →
                ENNReal.ofReal (c * Gp P.n P.m P.p P.Q) ≤ RN (A κ P) (Arr κ P) wl P.p P.N) := by sorry

end MixedORAM.PublicRead
