-- Prove2me | Theorems.Thm_MixedORAM_PublicRead_theorem_A_1
-- name    : MixedORAM.PublicRead.theorem_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:50:14.421514+00:00
-- url     : https://prove2.me/theorems/2c45705e-522b-4529-8ab2-dda59450ad11
-- title:
--   Theorem A.1 — tradeoff lower bounds (14) for public reads and (15) for private requests
-- statement:
--   Fix $\varepsilon,C_{\mathrm{mem}},\lambda>0$. There are $c>0$ and $n_0$ such that for all $n\ge n_0$, $m+1\le C_{\mathrm{mem}}n^{1-\varepsilon}$, $w\ge\lceil\log_2 n\rceil$, physical addresses of $a\le\lambda w$ bits, $0<p\le1/2$ and $N\ge4n/p$, every online implementation with $mw$ retained client bits and per-read correctness at least $2/3$ on every fixed full-API input satisfies, on the workload $\mathcal W_{R,W}$ with disclosed-kind privacy or $\mathcal W_{R,R}$ with hidden-kind privacy, for every initial array,
--   $$R_N\ge c,\qquad R_N\log_2\Big(2+\frac{\Pi_N}{R_N}+\frac{1-p}{p}\Big)\ge cH, \tag{14}$$
--   and on either workload with hidden-kind privacy also
--   $$\Pi_N\ge c,\qquad \Pi_N\log_2\Big(3+\frac{(1-p)R_N}{p\Pi_N}\Big)\ge cH. \tag{15}$$
--   The statistical statement needs only statistical privacy on horizon $N+2$ (total variation $1/16$). For computational privacy: for every computationally private family and every polynomial parameter bound and every choice of initial arrays on which the exact workload execution (preprocessing included) has polynomial expected probe count, the inequalities hold on those arrays for all sufficiently large $\kappa$, uniformly over parameters in the range that meet the assumptions (with $n\ge n_0$), with the same $c$.
--
--   Inverting (14) with Lemma C.1 gives Theorem 3.1.
--
--   Differences from the source:
--   - encoding: an online randomized implementation whose preprocessing and requests have independent random tapes (p. 14); a request's computation may flip coins → Impl: preprocessing is a law over (its probes, initial server memory, client state) given the initial array; each request runs a cell-probe decision tree drawn from a law that depends only on the retained state and the request; reason: a randomized program with internal coins is a mixture of deterministic decision trees; the paper's WLOG independent tapes (p. 14)
--   - generalization: the client retains at most mw bits, counting all transient state → only the client state kept between requests (and left by preprocessing) is bounded, by m·w bits (BitVec (m*w)); work inside one request is free; reason: every implementation of the source is one of these, so the Lean hypothesis is weaker; the proof's encoder sends only the retained post-epoch state (p. 16)
--   - encoding: O(w)-bit physical addresses → a-bit addresses (2^a cells, BitVec a) with a ≤ λw for a fixed λ > 0, the constants depending on λ; reason: Theorem A.1 (p. 14) makes the O(w) explicit as 'at most λw bits for a fixed λ'
--   - encoding: addresses in [n]; w ≥ ⌈log2 n⌉; words of w bits → Fin n (0-based) with [NeZero n]; Nat.clog 2 n ≤ w; BitVec w; reason: Lean conventions; n ≥ 1 is needed for a uniform address and holds for n ≥ n₀ ≥ 1
--   - encoding: real average costs Π_N, R_N → Π_N, R_N in [0, ∞] (ENNReal); the bound reads ENNReal.ofReal(c·G_p(Q)) ≤ R_N; reason: an expectation of a probe count may be infinite; R_N = ∞ satisfies the bound and Π_N ≤ Q forces finiteness; no finiteness hypothesis is added
--   - encoding: the inequalities (14), (15) between real numbers → with Π_N, R_N in [0, ∞]: R_N ≥ c (resp. Π_N ≥ c) in [0, ∞], and the logarithmic inequality as a real inequality unless R_N = ∞ or Π_N = ∞, where it holds with the value +∞; reason: an infinite cost makes the source's left side +∞; no finiteness hypothesis is added
--   - encoding: trace privacy: comparable inputs (same leakage, same initial array) have traces within total variation 1/16 on horizon N + 2 → StatPrivate k I (N + 2) (1/16): for every initial array and every two full-API request lists of length ≤ N + 2 with equal leakage (Leak_dis or Leak_hid), the laws of the observed traces (preprocessing probes, then the probes of each request) are within total variation 1/16; reason: §2.2 and Appendix G; 'comparable' needs equal leakage and the same initial array
--   - encoding: W_{R,W}, on which private kinds may be disclosed, or W_{R,R}, on which they must be hidden; (15) on either workload with hidden kinds → (14) for each workload under its leakage (disclosed on W_{R,W}, hidden on W_{R,R}); (15) for each workload under hidden-kind privacy; computationally, (14) under the workload's leakage or hidden kinds and (15) under hidden kinds; reason: hidden-kind privacy implies disclosed-kind privacy, so 'disclosed or hidden' on W_{R,W} is covered
--   - encoding: nonuniform polynomial-time samplers and distinguishers; polynomial probe cutoffs; negligible advantage (Appendix G) → samplers are polynomial-size multi-output circuit families (published LaconicBarrier.MCircuit) on uniform coins whose output is a fixed injective code of (A₀, u₀, u₁, z); distinguishers are the published NoisyOWMPC.Distinguisher (polynomial-size circuits); cutoffs b(κ) ≤ (κ+2)^c; advantage negligible in the sense of the published NoisyOWMPC.Negligible; reason: circuit families are the nonuniform polynomial-time model; randomness of a nonuniform distinguisher can be fixed to its best value
--   - reading: for each fixed secure family and fixed polynomial parameter bounds, the inequality holds for all sufficiently large κ, uniformly over parameters satisfying both those bounds and the theorem's assumptions (Appendix G, p. 76) → for every family A that is computationally private, every d, every choice Arr κ P of an initial array for each κ and P, and every exponent e bounding the expected probes (preprocessing included) of the exact workload execution from Arr κ P by (κ+2)^e over the parameter range, there is κ₀ such that for all κ ≥ κ₀ and all parameters P within (κ+2)^d (n, w, m, a, N, 1/p, Q) that meet the assumptions, including n ≥ n₀, the bound holds on the initial array Arr κ P with the same constant c; reason: Theorem A.1 says the computational case 'additionally' requires its conditions on top of 'for all sufficiently large n'; the expected-probe qualification is asked uniformly over the polynomial range, as Appendix G (p. 76) says, and only of the initial arrays the conclusion is about (a bound uniform over every initial array would be the narrower reading)
--   - generalization: p is efficiently samplable → no condition on p; reason: dropping a hypothesis gives a statement that specializes to the source's; a nonuniform sampler approximates any p with 1/p polynomial to within 2^{-κ} per request
-- source:
--   Ciszewski, Ragnoli, Access Cost Tradeoffs in Mixed-Mode Oblivious RAM, STOC 2027 submission (manuscript sha256 a4f849fd…), p. 14, Theorem A.1 (Eqs. (14), (15)); proof p. 19

import Mathlib
import Definitions.Def_MixedORAM_PublicRead_CompPrivacy
import Definitions.Def_MixedORAM_PublicRead_Frontier

set_option autoImplicit false

namespace MixedORAM.PublicRead

theorem theorem_A_1 (ε Cmem lam : ℝ) (hε : 0 < ε) (hC : 0 < Cmem) (hlam : 0 < lam) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      (∀ (n w m a N : ℕ) [NeZero n] (p : ℝ),
        n₀ ≤ n → (m : ℝ) + 1 ≤ Cmem * (n : ℝ) ^ (1 - ε) → Nat.clog 2 n ≤ w →
        (a : ℝ) ≤ lam * w → 0 < p → p ≤ 1 / 2 → 4 * (n : ℝ) / p ≤ N →
        ∀ I : Impl n w m a, I.Correct →
          (∀ wl : Workload, StatPrivate wl.leak I (N + 2) (1 / 16) →
            ∀ A₀ : Fin n → BitVec w,
              ENNReal.ofReal c ≤ RN I A₀ wl p N ∧
                (RN I A₀ wl p N = ⊤ ∨ PiN I A₀ wl p N = ⊤ ∨
                  c * Hn n m ≤ (RN I A₀ wl p N).toReal * Real.logb 2
                    (2 + (PiN I A₀ wl p N).toReal / (RN I A₀ wl p N).toReal + (1 - p) / p))) ∧
          (∀ wl : Workload, StatPrivate .hid I (N + 2) (1 / 16) →
            ∀ A₀ : Fin n → BitVec w,
              ENNReal.ofReal c ≤ PiN I A₀ wl p N ∧
                (PiN I A₀ wl p N = ⊤ ∨ RN I A₀ wl p N = ⊤ ∨
                  c * Hn n m ≤ (PiN I A₀ wl p N).toReal * Real.logb 2
                    (3 + (1 - p) * (RN I A₀ wl p N).toReal / (p * (PiN I A₀ wl p N).toReal))))) ∧
      (∀ (wl : Workload) (k : LeakKind), (k = wl.leak ∨ k = .hid) → ∀ A : Family, CompPrivate k A →
        ∀ (d : ℕ) (Arr : (κ : ℕ) → (P : Params) → Fin P.n → BitVec P.w),
          (∃ e : ℕ, ∀ (κ : ℕ) (P : Params) [NeZero P.n], P.Within d κ → n₀ ≤ P.n →
            (P.m : ℝ) + 1 ≤ Cmem * (P.n : ℝ) ^ (1 - ε) → Nat.clog 2 P.n ≤ P.w →
            (P.a : ℝ) ≤ lam * P.w → 0 < P.p → P.p ≤ 1 / 2 → 4 * (P.n : ℝ) / P.p ≤ P.N →
              expProbes (A κ P) (Arr κ P) wl P.p P.N ≤ ((κ + 2 : ℕ) : ENNReal) ^ e) →
          ∃ κ₀ : ℕ, ∀ κ ≥ κ₀, ∀ (P : Params) [NeZero P.n], P.Within d κ → n₀ ≤ P.n →
            (P.m : ℝ) + 1 ≤ Cmem * (P.n : ℝ) ^ (1 - ε) → Nat.clog 2 P.n ≤ P.w →
            (P.a : ℝ) ≤ lam * P.w → 0 < P.p → P.p ≤ 1 / 2 → 4 * (P.n : ℝ) / P.p ≤ P.N →
            (A κ P).Correct →
              let A₀ := Arr κ P;
                (ENNReal.ofReal c ≤ RN (A κ P) A₀ wl P.p P.N ∧
                  (RN (A κ P) A₀ wl P.p P.N = ⊤ ∨ PiN (A κ P) A₀ wl P.p P.N = ⊤ ∨
                    c * Hn P.n P.m ≤ (RN (A κ P) A₀ wl P.p P.N).toReal * Real.logb 2
                      (2 + (PiN (A κ P) A₀ wl P.p P.N).toReal / (RN (A κ P) A₀ wl P.p P.N).toReal +
                        (1 - P.p) / P.p))) ∧
                (k = .hid →
                  ENNReal.ofReal c ≤ PiN (A κ P) A₀ wl P.p P.N ∧
                    (PiN (A κ P) A₀ wl P.p P.N = ⊤ ∨ RN (A κ P) A₀ wl P.p P.N = ⊤ ∨
                      c * Hn P.n P.m ≤ (PiN (A κ P) A₀ wl P.p P.N).toReal * Real.logb 2
                        (3 + (1 - P.p) * (RN (A κ P) A₀ wl P.p P.N).toReal /
                          (P.p * (PiN (A κ P) A₀ wl P.p P.N).toReal))))) := by sorry

end MixedORAM.PublicRead
