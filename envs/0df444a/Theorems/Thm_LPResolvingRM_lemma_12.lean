-- Prove2me | Theorems.Thm_LPResolvingRM_lemma_12
-- name    : LPResolvingRM.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:44:15.463269+00:00
-- url     : https://prove2.me/theorems/e3e7dc92-4ae6-44f2-b41f-f44b45940fc1
-- title:
--   Lemma 12 — the frozen process $\tilde b$ leaves $\mathfrak B$ before $t$ with probability at most $2me^{-L^2(T-t)/8}$
-- statement:
--   Under Assumptions 1 and 2 with $m\ge1$, the optimal solution $y^*$ of (6), a stability radius $L\in(0,1]$ with $L\le\underline b=\min_ib_i$ and $\underline b<1+L$, and any optimal solution rule for LP (5): for all $T\ge T_1$ and $t\le T-2$,
--   $$\mathbb P\big(\tilde b_s\notin\mathfrak B\text{ for some }s\le t\big)\le2me^{-L^2(T-t)/8},$$
--   where $T_1$ is the minimal integer such that $T_1\ge\big(\frac1{\exp(L/8)-1}+2\big)\vee\big(\frac1{\exp(L/(8(1+L-\underline b)))-1}+2\big)$ and $\frac{\log T_1}{T_1^{1/4}}\le\frac{\kappa^{1/4}L}4$, with $\kappa=(1-\exp(-\frac L8))\wedge(1-\exp(-\frac L{8(1+L-\underline b)}))$.
--
--   This is the first component of the decomposition (30) of $\mathbb P(\tau_S\le t)$.
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
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, Lemma 12, p.36 (proof C.2, pp.37–39)

import Definitions.Def_LPResolvingRM_IsStabilityRadius
import Definitions.Def_LPResolvingRM_goodEvent

namespace LPResolvingRM

/-- **Lemma 12** (arXiv:2101.11092v3, Appendix C.1, p.36): "The following inequality holds for
all T ≥ T₁ and t ≤ T − 2,"

`P(b̃_s ∉ 𝔅 for some s ≤ t) ≤ 2m e^{−L²(T−t)/8}`,

where `T₁` is the minimal integer with `T₁ ≥ (1/(exp(L/8) − 1) + 2) ∨ (1/(exp(L/(8(1+L−b̲))) − 1)
+ 2)` and `log T₁/T₁^{1/4} ≤ κ^{1/4}L/4`, and `κ = (1 − exp(−L/8)) ∧ (1 − exp(−L/(8(1+L−b̲))))`.

**Formalization Note.** Under Assumptions 1 and 2 with the optimal `y*` of (6), a stability
radius `L` (reading R1) and an optimal rule `sel` for LP (5); `b̃`, `τ̃`, `𝓔_t` and `𝔅` are the C.1
objects (`LPResolvingRM.bTilde`). `m ≥ 1` (for `b̲ = min_i b_i`), and `b̲ < 1 + L`: the paper's
`κ` and `ϵ'` are defined (positive) only then. `s` ranges over the periods `1, …, t`. -/
theorem lemma_12 {n m : ℕ} (I : Instance n m) (h1 : Assumption1 I) (h2 : Assumption2 I)
    (hm : 0 < m) (ystar : Fin n → ℝ) (hystar : LPAllocRM.IsLPOptimal (normC I) I.b 1 (normMu I) ystar)
    (L : ℝ) (hL0 : 0 < L) (hL1 : L ≤ 1) (hLb : ∀ i, L ≤ I.b i)
    (hstab : IsStabilityRadius I L) (hκ : bmin I < 1 + L)
    (sel : Selector n m) (hsel : IsSelector I sel)
    (T : ℕ) (hT : T1 I L ≤ T) (t : ℕ) (ht : t + 2 ≤ T) :
    prob I sel T (fun ω β =>
        ∃ s, 1 ≤ s ∧ s ≤ t ∧ ¬ region I ystar L (bTilde I sel ystar L T ω β s)) ≤
      2 * m * Real.exp (-(L ^ 2 * ((T : ℝ) - t) / 8)) := by sorry

end LPResolvingRM
