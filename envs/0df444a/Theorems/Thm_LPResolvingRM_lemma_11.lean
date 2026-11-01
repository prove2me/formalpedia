-- Prove2me | Theorems.Thm_LPResolvingRM_lemma_11
-- name    : LPResolvingRM.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:44:38.264987+00:00
-- url     : https://prove2.me/theorems/3f6c1214-a2d1-414a-9bae-79762003911a
-- title:
--   Lemma 11 — the summed bad-event probabilities
-- statement:
--   Under the hypotheses of Lemma 13, for every $T\in\mathbb N_+$,
--   $$\sum_{t=1}^T\sum_{s=\kappa T+1}^t\mathbb P(\bar{\mathcal E}_s)\le\frac{nT}{L^2}\exp(-2L^2\kappa T)+4n^3T^{3/2}\exp\Big(-\frac1{n^2}(\kappa T)^{1/2}\Big). \tag{18}$$
--
--   This bounds the second component of the decomposition (30), summed over the horizon.
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
--   - generalization: stated in §3 under Assumption 3 (all constraints binding), with 𝔅 = ⨂_i [b_i − L, b_i + L] → without Assumption 3, with the general-case 𝔅, τ_S (and 𝓔_t) of Appendix C.1; reason: Appendix C applies it in the general case (pp.40–41); when every constraint binds, the C.1 objects are the §3 ones
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, Lemma 11, (18), p.29 (used in the general case, C.3, p.40)

import Definitions.Def_LPResolvingRM_IsStabilityRadius
import Definitions.Def_LPResolvingRM_goodEvent

namespace LPResolvingRM

/-- **Lemma 11** (arXiv:2101.11092v3, Appendix A.7, (18), p.29; used for the general case in
C.3, p.40): "The following inequality holds for T ∈ ℕ⁺"

`∑_{t=1}^{T} ∑_{s=κT+1}^{t} P(𝓔̄_s) ≤ (nT/L²) exp(−2L²κT) + 4n³T^{3/2} exp(−(1/n²)(κT)^{1/2})`.

**Formalization Note.** `𝓔_s` is the general-case good event (`LPResolvingRM.goodEvent`, p.35),
under the hypotheses of Lemma 13. `κT` enters as `⌊κT⌋` (p.12); the inner sum runs over the
periods `s` with `⌊κT⌋ < s ≤ t` (empty when `t ≤ κT`). -/
theorem lemma_11 {n m : ℕ} (I : Instance n m) (h1 : Assumption1 I) (h2 : Assumption2 I)
    (hm : 0 < m) (ystar : Fin n → ℝ) (hystar : LPAllocRM.IsLPOptimal (normC I) I.b 1 (normMu I) ystar)
    (L : ℝ) (hL0 : 0 < L) (hL1 : L ≤ 1) (hLb : ∀ i, L ≤ I.b i)
    (hstab : IsStabilityRadius I L) (hκ : bmin I < 1 + L)
    (sel : Selector n m) (hsel : IsSelector I sel) (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Finset.Icc 1 T, ∑ s ∈ (Finset.Icc 1 t).filter (fun s => kT I L T < s),
        prob I sel T (fun ω _ => ¬ goodEvent I sel ystar L T ω s) ≤
      n * T / L ^ 2 * Real.exp (-(2 * L ^ 2 * (kT I L T : ℝ))) +
        4 * (n : ℝ) ^ 3 * (T : ℝ) ^ (3 / 2 : ℝ) *
          Real.exp (-(1 / (n : ℝ) ^ 2 * (kT I L T : ℝ) ^ (1 / 2 : ℝ))) := by sorry

end LPResolvingRM
