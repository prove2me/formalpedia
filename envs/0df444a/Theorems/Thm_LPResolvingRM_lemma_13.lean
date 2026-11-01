-- Prove2me | Theorems.Thm_LPResolvingRM_lemma_13
-- name    : LPResolvingRM.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:44:22.677468+00:00
-- url     : https://prove2.me/theorems/981e3de0-e5ca-49d6-bac9-207a7130c87b
-- title:
--   Lemma 13 — $\mathcal A\cap\mathcal B\subset\mathcal E_t$, the probability of $\mathcal E_t$, and the lower bound on $\mathbb E[\tau_S]$
-- statement:
--   Under the hypotheses of Lemma 12 (Assumptions 1 and 2, $m\ge1$, a stability radius $L\in(0,1]$ with $L\le\underline b<1+L$, any optimal solution rule for LP (5)):
--
--   1. $\big(\bigcap_{j=1}^n\mathcal A^{(j)}_t\big)\cap\big(\bigcap_{j=1}^n\mathcal B^{(j)}_t\big)\subset\mathcal E_t$ for $t=1,\dots,T$;
--   2. for $1\le t\le T-2$,
--   $$\mathbb P(\mathcal E_t)\ \begin{cases}=1&t\le\kappa T,\\ \ge1-2n\exp(-2L^2(t-1))-2n\exp\big(-\frac{2(t-1)^{1/2}}{n^2}\big)&t>\kappa T;\end{cases}$$
--   3. for $T\ge T_1$,
--   $$\mathbb E[\tau_S]\ge T-2-\frac{16m}{L^2}-\frac{nT}{L^2}\exp(-2L^2\kappa T)-4n^3T^{3/2}\exp\Big(-\frac{\kappa^{1/2}}{n^2}T^{1/2}\Big).$$
--
--   Item 3 is what turns the analysis of the constraint process into the bound on the last two terms of Corollary 1.
--
--   Differences from the source:
--   - encoding: (r_t, a_t) i.i.d. from P on the support {(µ_j, c_j)} → the type index j_t of each period i.i.d. with law p on Fin n, and (r_t, a_t) = (µ_{j_t}, c_{j_t}); reason: drawing the index gives the same law of (r_t, a_t)
--   - encoding: P takes the finite support {(µ_j, c_j)} → p_j > 0 for every j and ∑_j p_j = 1; reason: a support point has positive probability; p is a probability vector
--   - generalization: distinct support points (µ_j, c_j) → the pairs (µ_j, c_j) need not be distinct; the algorithm counts each index separately; reason: on distinct pairs this is the paper's model; the proofs never use distinctness
--   - encoding: E[·] over the arrivals and the algorithm's randomization → a finite sum over type sequences (Fin n)^T and coin sequences Bool^T weighted by the path probability; reason: all randomness is finite; same expectation
--   - encoding: periods t = 1, …, T, types 1..n, resources 1..m → Lean periods k = t − 1 : Fin T, types Fin n, resources Fin m; B_t is cap (t − 1), b_t is avgCap (t − 1); reason: index shift only
--   - reading: the optimal solution y*_t of LP (5) (tie-break unspecified) → every rule sel that maps (empirical frequencies, right-hand side ≥ 0) to an optimal solution of LP (5); reason: LP (5) may have several optima; the statement holds for every tie-breaking rule that is a function of the LP's data, including the paper's
--   - reading: Algorithm 1 line 3: set x₁ = 1 → x₁ = 1 when the constraint permits (c_{j₁} ≤ B₁), else 0; reason: no shorting is allowed (p.7); if B_{i,1} ≤ 1 for some i then τ = 0, otherwise c_{j₁} ≤ 1 < B₁, so the regret is unchanged
--   - reading: L, the constant of Lemma 1 → any L with 0 < L ≤ 1, L ≤ min_i b_i and IsStabilityRadius L; reason: reading R1: the proofs use only Lemma 1's property and the WLOGs L ≤ 1 (p.26), 1 + L − b̲ ≤ 1 (p.40); the property is monotone in L, so the L of Lemma 1 can be shrunk to such an L
--   - reading: κ = (1 − exp(−L/8)) ∧ (1 − exp(−L/(8(1+L−b̲)))) and ϵ′ = 1 + L − b̲ → hypotheses m ≥ 1 and b̲ < 1 + L; reason: κ and ϵ′ are the intended positive constants only when 1 + L − b̲ > 0 (division by zero at equality, κ ≤ 0 and κ^{1/4} undefined beyond); b̲ = min_i b_i needs m ≥ 1. Under Assumption 3 every b_i ≤ 1 < 1 + L
--   - encoding: sup_{b′∈𝔅} of E[a_t x_t(b′) | H_{t−1}] − b′ → for every b′ ∈ 𝔅, ∑_j p_j c_j y_{j,t}(b′) − b′ with y_t(b′) = 1 at t = 1 and sel(n_{t−1}/(t−1), b′) for t ≥ 2; reason: the conditional expectation given the history is this explicit sum (p.15, (13)); a 'for all' avoids a junk sSup over the unbounded 𝔅
--   - reading: κT, assumed an integer 'without loss of generality' (p.12) → ⌊κT⌋ wherever κT enters as a number; the comparisons t ≤ κT are unchanged for integer t; reason: the paper's WLOG; equal to κT in the case the paper treats
--   - reading: 'Consequently, E[τ_S] ≥ …' (no range of T stated) → for T ≥ T₁; reason: the bound follows from Lemma 12 (p.40), which holds for T ≥ T₁
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, Lemma 13, pp.36–37 (proof C.3, p.40)

import Definitions.Def_LPResolvingRM_IsStabilityRadius
import Definitions.Def_LPResolvingRM_goodEvent

namespace LPResolvingRM

/-- **Lemma 13** (arXiv:2101.11092v3, Appendix C.1, pp.36–37): "We have
(∩ⁿⱼ₌₁𝒜⁽ʲ⁾ₜ) ∩ (∩ⁿⱼ₌₁ℬ⁽ʲ⁾ₜ) ⊂ 𝓔ₜ for t = 1, ..., T. Under Assumption 1 and 2, we have for
t ≤ T − 2,"

`P(𝓔_t) = 1` for `t ≤ κT` and `P(𝓔_t) ≥ 1 − 2n exp(−2L²(t − 1)) − 2n exp(−2(t−1)^{1/2}/n²)` for
`t > κT`; "Consequently,"

`E[τ_S] ≥ T − 2 − 16m/L² − (nT/L²) exp(−2L²κT) − 4n³T^{3/2} exp(−(κ^{1/2}/n²)·T^{1/2})`.

**Formalization Note.** Three conclusions, in order. The `E[τ_S]` bound rests on Lemma 12 and is
read for `T ≥ T₁`. `κT` enters as `⌊κT⌋` (p.12: "we assume κT takes an integer value"); the case
split `t ≤ κT` is the same for integer `t`, and `κ^{1/2}T^{1/2} = (κT)^{1/2}`. Hypotheses as in
Lemma 12 (`m ≥ 1`, `b̲ < 1 + L` for `κ` and `ϵ'` to be defined). -/
theorem lemma_13 {n m : ℕ} (I : Instance n m) (h1 : Assumption1 I) (h2 : Assumption2 I)
    (hm : 0 < m) (ystar : Fin n → ℝ) (hystar : LPAllocRM.IsLPOptimal (normC I) I.b 1 (normMu I) ystar)
    (L : ℝ) (hL0 : 0 < L) (hL1 : L ≤ 1) (hLb : ∀ i, L ≤ I.b i)
    (hstab : IsStabilityRadius I L) (hκ : bmin I < 1 + L)
    (sel : Selector n m) (hsel : IsSelector I sel) :
    (∀ (T : ℕ) (ω : Fin T → Fin n) (t : ℕ), 1 ≤ t → t ≤ T →
        (∀ j, eventA I L T ω t j) → (∀ j, eventB I T ω t j) →
        goodEvent I sel ystar L T ω t) ∧
    (∀ T t : ℕ, 1 ≤ t → t + 2 ≤ T →
        (t ≤ kT I L T → prob I sel T (fun ω _ => goodEvent I sel ystar L T ω t) = 1) ∧
        (kT I L T < t →
          1 - 2 * n * Real.exp (-(2 * L ^ 2 * ((t : ℝ) - 1))) -
              2 * n * Real.exp (-(2 * ((t : ℝ) - 1) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2)) ≤
            prob I sel T (fun ω _ => goodEvent I sel ystar L T ω t))) ∧
    (∀ T : ℕ, T1 I L ≤ T →
        (T : ℝ) - 2 - 16 * m / L ^ 2 -
            n * T / L ^ 2 * Real.exp (-(2 * L ^ 2 * (kT I L T : ℝ))) -
            4 * (n : ℝ) ^ 3 * (T : ℝ) ^ (3 / 2 : ℝ) *
              Real.exp (-((kT I L T : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2)) ≤
          expect I sel T (fun ω β => (tauS I ystar L T ω β : ℝ))) := by sorry

end LPResolvingRM
