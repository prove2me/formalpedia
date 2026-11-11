-- Prove2me | Theorems.Thm_MixedORAM_PublicRead_lemma_4_1
-- name    : MixedORAM.PublicRead.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:49:48.865799+00:00
-- url     : https://prove2.me/theorems/273819f4-fe1e-419f-9b06-7780826d34b7
-- title:
--   Lemma 4.1 — per-epoch edge bound E_ref D_I + E_ref E_I/(ηpℓ) ≥ c
-- statement:
--   Fix $\varepsilon>0$, $C_{\mathrm{mem}}>0$ and $\lambda>0$. There are constants $C,c,\eta>0$, independent of $p$, and a threshold $n_0$ such that the following holds. Let $n\ge n_0$, $m+1\le C_{\mathrm{mem}}n^{1-\varepsilon}$, $w\ge\lceil\log_2 n\rceil$, $a\le\lambda w$, $0<p\le1/2$ and $N\ge 4n/p$. Let $I$ be an implementation with $mw$ retained client bits and $a$-bit addresses that has per-read correctness at least $2/3$ on every fixed full-API input, and trace privacy on the workload: disclosed-kind privacy on $\mathcal W_{R,W}$, hidden-kind privacy on $\mathcal W_{R,R}$ (statistically: total variation $1/16$ on horizon $N+2$). Then for every initial array and every epoch $I$ of length $\ell\ge\ell_0=\lceil C(m+1)/p\rceil$ inside the window of length $\omega=\lfloor n/(128p)\rfloor$ at a fixed position relative to the endpoint,
--   $$\mathbb E_{\mathrm{ref}}D_I+\frac{\mathbb E_{\mathrm{ref}}E_I}{\eta p\ell}\ \ge\ c .$$
--   The expectations are over the reference terminal experiment of §4.1 (its endpoint, prefix, terminal address and the implementation's randomness), conditioned only on $G_0$.
--
--   The same holds with computational privacy: for every computationally private family and every polynomial parameter bound and every choice of initial arrays on which the exact workload execution has polynomial expected probe count, the bound holds on those arrays for all sufficiently large $\kappa$, uniformly over the parameters in the range that meet the assumptions above (with $n\ge n_0$), with the same $C,c,\eta$.
--
--   Summed over geometric epochs (Lemma A.6), this bound gives the tradeoff of Theorem A.1.
--
--   Differences from the source:
--   - encoding: an online randomized implementation whose preprocessing and requests have independent random tapes (p. 14); a request's computation may flip coins → Impl: preprocessing is a law over (its probes, initial server memory, client state) given the initial array; each request runs a cell-probe decision tree drawn from a law that depends only on the retained state and the request; reason: a randomized program with internal coins is a mixture of deterministic decision trees; the paper's WLOG independent tapes (p. 14)
--   - generalization: the client retains at most mw bits, counting all transient state → only the client state kept between requests (and left by preprocessing) is bounded, by m·w bits (BitVec (m*w)); work inside one request is free; reason: every implementation of the source is one of these, so the Lean hypothesis is weaker; the proof's encoder sends only the retained post-epoch state (p. 16)
--   - encoding: O(w)-bit physical addresses → a-bit addresses (2^a cells, BitVec a) with a ≤ λw for a fixed λ > 0, the constants depending on λ; reason: Theorem A.1 (p. 14) makes the O(w) explicit as 'at most λw bits for a fixed λ'
--   - encoding: addresses in [n]; w ≥ ⌈log2 n⌉; words of w bits → Fin n (0-based) with [NeZero n]; Nat.clog 2 n ≤ w; BitVec w; reason: Lean conventions; n ≥ 1 is needed for a uniform address and holds for n ≥ n₀ ≥ 1
--   - encoding: trace privacy: comparable inputs (same leakage, same initial array) have traces within total variation 1/16 on horizon N + 2 → StatPrivate k I (N + 2) (1/16): for every initial array and every two full-API request lists of length ≤ N + 2 with equal leakage (Leak_dis or Leak_hid), the laws of the observed traces (preprocessing probes, then the probes of each request) are within total variation 1/16; reason: §2.2 and Appendix G; 'comparable' needs equal leakage and the same initial array
--   - generalization: under the assumptions of Theorem 3.1 (m ≤ n^{1−ε}, a private budget), with m + 1 ≤ C_mem n^{1−ε} → only m + 1 ≤ C_mem n^{1−ε}; no budget hypothesis; reason: Theorem 3.1's budget is not used by the lemma, and m ≤ n^{1−ε} is the case C_mem = 2; fewer hypotheses give a statement that specializes to the source's
--   - encoding: every epoch I of length ℓ ≥ ℓ₀ inside the window [e − ω + 1, e], at a fixed position relative to e; V = {⌈N/2⌉, …, N − 1} → offsets (s, ℓ) with ℓ₀ ≤ ℓ and s + ℓ ≤ ω, the epoch being [e − s − ℓ + 1, e − s]; V = Finset.Icc ((N + 1)/2) (N − 1); 0-based positions; reason: the same epochs; (N + 1)/2 = ⌈N/2⌉ for natural N
--   - encoding: E_ref D_I + E_ref E_I/(ηpℓ) ≥ c, expectations conditioned on G₀ → ENNReal.ofReal c ≤ refExp(D_I) + refExp(E_I) / ENNReal.ofReal(η p ℓ), refExp the ratio of the weight on G₀ to Pr(G₀); reason: expectations of counts in [0, ∞]
--   - encoding: nonuniform polynomial-time samplers and distinguishers; polynomial probe cutoffs; negligible advantage (Appendix G) → samplers are polynomial-size multi-output circuit families (published LaconicBarrier.MCircuit) on uniform coins whose output is a fixed injective code of (A₀, u₀, u₁, z); distinguishers are the published NoisyOWMPC.Distinguisher (polynomial-size circuits); cutoffs b(κ) ≤ (κ+2)^c; advantage negligible in the sense of the published NoisyOWMPC.Negligible; reason: circuit families are the nonuniform polynomial-time model; randomness of a nonuniform distinguisher can be fixed to its best value
--   - reading: for each fixed secure family and fixed polynomial parameter bounds, the inequality holds for all sufficiently large κ, uniformly over parameters satisfying both those bounds and the theorem's assumptions (Appendix G, p. 76) → for every family A that is computationally private, every d, every choice Arr κ P of an initial array for each κ and P, and every exponent e bounding the expected probes (preprocessing included) of the exact workload execution from Arr κ P by (κ+2)^e over the parameter range, there is κ₀ such that for all κ ≥ κ₀ and all parameters P within (κ+2)^d (n, w, m, a, N, 1/p, Q) that meet the assumptions, including n ≥ n₀, the bound holds on the initial array Arr κ P with the same constant c; reason: Theorem A.1 says the computational case 'additionally' requires its conditions on top of 'for all sufficiently large n'; the expected-probe qualification is asked uniformly over the polynomial range, as Appendix G (p. 76) says, and only of the initial arrays the conclusion is about (a bound uniform over every initial array would be the narrower reading)
--   - generalization: p is efficiently samplable; budgets have polynomial-length descriptions → no condition on how p and Q are described; reason: dropping hypotheses gives a stronger statement that specializes to the source's; a nonuniform sampler approximates any p with 1/p polynomial to within 2^{-κ} per request, and Q enters only the final algebra
-- source:
--   Ciszewski, Ragnoli, Access Cost Tradeoffs in Mixed-Mode Oblivious RAM, STOC 2027 submission (manuscript sha256 a4f849fd…), pp. 9–10, Lemma 4.1 (Eq. (11)); proof pp. 16–17

import Mathlib
import Definitions.Def_MixedORAM_PublicRead_CompPrivacy
import Definitions.Def_MixedORAM_PublicRead_Epochs

set_option autoImplicit false

namespace MixedORAM.PublicRead

theorem lemma_4_1 (ε Cmem lam : ℝ) (hε : 0 < ε) (hC : 0 < Cmem) (hlam : 0 < lam) :
    ∃ C c η : ℝ, 0 < C ∧ 0 < c ∧ 0 < η ∧ ∃ n₀ : ℕ,
      (∀ (wl : Workload) (n w m a N : ℕ) [NeZero n] (p : ℝ),
        n₀ ≤ n → (m : ℝ) + 1 ≤ Cmem * (n : ℝ) ^ (1 - ε) → Nat.clog 2 n ≤ w →
        (a : ℝ) ≤ lam * w → 0 < p → p ≤ 1 / 2 → 4 * (n : ℝ) / p ≤ N →
        ∀ I : Impl n w m a, I.Correct → StatPrivate wl.leak I (N + 2) (1 / 16) →
          ∀ (A₀ : Fin n → BitVec w) (s ℓ : ℕ), ell0 C m p ≤ ℓ → s + ℓ ≤ omegaW n p →
            ENNReal.ofReal c ≤
              refExp I A₀ wl p N (fun e _ res => (edgesD e s ℓ (traceOf res) : ENNReal)) +
                refExp I A₀ wl p N (fun e _ res => (edgesE e s ℓ (traceOf res) : ENNReal)) /
                  ENNReal.ofReal (η * p * ℓ)) ∧
      (∀ (wl : Workload) (A : Family), CompPrivate wl.leak A →
        ∀ (d : ℕ) (Arr : (κ : ℕ) → (P : Params) → Fin P.n → BitVec P.w),
          (∃ e : ℕ, ∀ (κ : ℕ) (P : Params) [NeZero P.n], P.Within d κ → n₀ ≤ P.n →
            (P.m : ℝ) + 1 ≤ Cmem * (P.n : ℝ) ^ (1 - ε) → Nat.clog 2 P.n ≤ P.w →
            (P.a : ℝ) ≤ lam * P.w → 0 < P.p → P.p ≤ 1 / 2 → 4 * (P.n : ℝ) / P.p ≤ P.N →
              expProbes (A κ P) (Arr κ P) wl P.p P.N ≤ ((κ + 2 : ℕ) : ENNReal) ^ e) →
          ∃ κ₀ : ℕ, ∀ κ ≥ κ₀, ∀ (P : Params) [NeZero P.n], P.Within d κ → n₀ ≤ P.n →
            (P.m : ℝ) + 1 ≤ Cmem * (P.n : ℝ) ^ (1 - ε) → Nat.clog 2 P.n ≤ P.w →
            (P.a : ℝ) ≤ lam * P.w → 0 < P.p → P.p ≤ 1 / 2 → 4 * (P.n : ℝ) / P.p ≤ P.N →
            (A κ P).Correct →
              ∀ s ℓ : ℕ, ell0 C P.m P.p ≤ ℓ →
                s + ℓ ≤ omegaW P.n P.p →
                ENNReal.ofReal c ≤
                  refExp (A κ P) (Arr κ P) wl P.p P.N
                      (fun e _ res => (edgesD e s ℓ (traceOf res) : ENNReal)) +
                    refExp (A κ P) (Arr κ P) wl P.p P.N
                        (fun e _ res => (edgesE e s ℓ (traceOf res) : ENNReal)) /
                      ENNReal.ofReal (η * P.p * ℓ)) := by sorry

end MixedORAM.PublicRead
