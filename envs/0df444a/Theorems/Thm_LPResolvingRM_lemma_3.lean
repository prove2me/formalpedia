-- Prove2me | Theorems.Thm_LPResolvingRM_lemma_3
-- name    : LPResolvingRM.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:43:06.862014+00:00
-- url     : https://prove2.me/theorems/10997034-6b30-4276-a10d-f697f9da8c1e
-- title:
--   Lemma 3 — $\mathbb E[T-\tau_S]$ and the last two terms of Corollary 1 (corrected: $\|\lambda^*\|_1\to\max\{\|\lambda^*\|_1,\max_j|\mu_j-c_j^\top\lambda^*|\}$)
-- statement:
--   Under Assumptions 1 and 2, with the optimal solution $y^*$ of (6), a dual optimal $(\lambda^*,\gamma^*)$ of (7), a stability radius $L\in(0,1]$ with $L\le\min_ib_i$, any optimal solution rule for LP (5) and $T\ge1$:
--
--   1. $\displaystyle\mathbb E[T-\tau_S]\le\sum_{t=1}^T\mathbb P\big(b_s\notin\mathfrak B\text{ for some }s\le t\big)$;
--   2. with $\Lambda=\max\{\|\lambda^*\|_1,\max_{j\in[n]}|\mu_j-c_j^\top\lambda^*|\}$,
--   $$(T-\mathbb E[\tau_S])\max_{j\in[n]}|\mu_j-c_j^\top\lambda^*|+\lambda^{*\top}\mathbb E[B_{\tau_S}]\le\Lambda\cdot\big(3\,\mathbb E[T-\tau_S]+4\big).$$
--
--   Here $B_{\tau_S}$ is the capacity at the beginning of period $\tau_S$ ($B_{T+1}$ if $\tau_S=T+1$).
--
--   Differences from the source:
--   - correction: ‖λ*‖₁·(3E[T − τ_S] + 4) → Λ·(3E[T − τ_S] + 4) with Λ = max{‖λ*‖₁, max_j |µ_j − c_jᵀλ*|}; reason: the printed bound is false: (µ, c) = (1, 1), (0.01, 1), p = (½, ½), b = ¾ satisfy Assumptions 1–3, λ* = 0.01, max_j|µ_j − c_jλ*| = 0.99, and any stability radius L ≤ 0.005 gives τ_S ≤ T − 1, so the left side is ≥ 0.99·E[T − τ_S] > 0.01·(3E[T − τ_S] + 4); the proof's step max_j|µ_j − c_jᵀλ*| ≤ ‖λ*‖₁ (p.25) is false, and its chain gives Λ
--   - encoding: (r_t, a_t) i.i.d. from P on the support {(µ_j, c_j)} → the type index j_t of each period i.i.d. with law p on Fin n, and (r_t, a_t) = (µ_{j_t}, c_{j_t}); reason: drawing the index gives the same law of (r_t, a_t)
--   - encoding: P takes the finite support {(µ_j, c_j)} → p_j > 0 for every j and ∑_j p_j = 1; reason: a support point has positive probability; p is a probability vector
--   - generalization: distinct support points (µ_j, c_j) → the pairs (µ_j, c_j) need not be distinct; the algorithm counts each index separately; reason: on distinct pairs this is the paper's model; the proofs never use distinctness
--   - encoding: E[·] over the arrivals and the algorithm's randomization → a finite sum over type sequences (Fin n)^T and coin sequences Bool^T weighted by the path probability; reason: all randomness is finite; same expectation
--   - encoding: periods t = 1, …, T, types 1..n, resources 1..m → Lean periods k = t − 1 : Fin T, types Fin n, resources Fin m; B_t is cap (t − 1), b_t is avgCap (t − 1); reason: index shift only
--   - reading: the optimal solution y*_t of LP (5) (tie-break unspecified) → every rule sel that maps (empirical frequencies, right-hand side ≥ 0) to an optimal solution of LP (5); reason: LP (5) may have several optima; the statement holds for every tie-breaking rule that is a function of the LP's data, including the paper's
--   - reading: Algorithm 1 line 3: set x₁ = 1 → x₁ = 1 when the constraint permits (c_{j₁} ≤ B₁), else 0; reason: no shorting is allowed (p.7); if B_{i,1} ≤ 1 for some i then τ = 0, otherwise c_{j₁} ≤ 1 < B₁, so the regret is unchanged
--   - encoding: λ*, the dual optimal solution of (7) → the λ-part of any dual optimal (λ, γ) of (7); reason: the dual optimum is unique when the primal optimum is nondegenerate (Assumption 2); same instances
--   - reading: L, the constant of Lemma 1 → any L with 0 < L ≤ 1, L ≤ min_i b_i and IsStabilityRadius L; reason: reading R1: the proofs use only Lemma 1's property and the WLOGs L ≤ 1 (p.26), 1 + L − b̲ ≤ 1 (p.40); the property is monotone in L, so the L of Lemma 1 can be shrunk to such an L
--   - generalization: stated in §3 under Assumption 3 (all constraints binding), with 𝔅 = ⨂_i [b_i − L, b_i + L] → without Assumption 3, with the general-case 𝔅, τ_S (and 𝓔_t) of Appendix C.1; reason: Appendix C applies it in the general case (pp.40–41); when every constraint binds, the C.1 objects are the §3 ones
--   - reading: τ_S as displayed in §3.2 (p.11), with 'b_{i,t} − b_i > −L for some i ∈ I′' → the C.1 definition (p.35), b_{i,t} − b_i < −L, i.e. τ_S = min{t ≤ T : b_t ∉ 𝔅} ∪ {T + 1}; reason: the §3.2 sign is a typo; C.1 restates it with '< −L' and Appendix C uses that
--   - encoding: n_j(τ_S), n^a_j(τ_S) at τ_S = T + 1 → the counts over the whole horizon (no orders after T); reason: n_j(T + 1) = n_j(T) since no order arrives after T
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, Lemma 3, p.13 (proof A.4, p.25; applied in C.4, p.40)

import Definitions.Def_LPResolvingRM_DualOptimal
import Definitions.Def_LPResolvingRM_IsStabilityRadius
import Definitions.Def_LPResolvingRM_tauS

namespace LPResolvingRM

/-- **Lemma 3 (corrected second inequality: `‖λ*‖₁ → Λ`)** (arXiv:2101.11092v3, p.13; general
case as used in Appendix C.4, p.40): under Assumptions 1 and 2 with a stability radius `L`,

1. `E[T − τ_S] ≤ ∑_{t=1}^{T} P(b_s ∉ 𝔅 for some s ≤ t)`;
2. `(T − E[τ_S])·max_{j∈[n]} |μ_j − c_jᵀλ*| + λ*ᵀ·E[B_{τ_S}] ≤ Λ·(3E[T − τ_S] + 4)`, where
   `Λ = max{‖λ*‖₁, max_j |μ_j − c_jᵀλ*|}`.

**Formalization Note.** The printed constant `‖λ*‖₁` in 2. is false (`(μ, c) = (1, 1),
(0.01, 1)`, `p = (½, ½)`, `b = ¾`: `λ* = 0.01`, `max_j|μ_j − c_jλ*| = 0.99`, `E[T − τ_S] ≥ 1`);
the proof's own chain gives `Λ`. `𝔅` and `τ_S` are the C.1 objects; `s` ranges over the periods
`1, …, s ≤ t`; `B_{τ_S}` is the beginning-of-period capacity `cap … (τ_S − 1)` (as in the proof,
`B_{τ_S} ≤ (T − τ_S + 2) b_{τ_S−1}`), with `B_{T+1}` when `τ_S = T + 1`. -/
theorem lemma_3 {n m : ℕ} (I : Instance n m) (h1 : Assumption1 I) (h2 : Assumption2 I)
    (lam : Fin m → ℝ) (γ : Fin n → ℝ) (hdual : DualOptimal I lam γ)
    (ystar : Fin n → ℝ) (hystar : LPAllocRM.IsLPOptimal (normC I) I.b 1 (normMu I) ystar)
    (L : ℝ) (hL0 : 0 < L) (hL1 : L ≤ 1) (hLb : ∀ i, L ≤ I.b i)
    (hstab : IsStabilityRadius I L) (sel : Selector n m) (hsel : IsSelector I sel)
    (T : ℕ) (hT : 1 ≤ T) :
    expect I sel T (fun ω β => (T : ℝ) - tauS I ystar L T ω β) ≤
        ∑ t ∈ Finset.Icc 1 T, prob I sel T (fun ω β =>
          ∃ s, 1 ≤ s ∧ s ≤ t ∧ ¬ region I ystar L (avgCap I T ω β (s - 1))) ∧
      ((T : ℝ) - expect I sel T (fun ω β => (tauS I ystar L T ω β : ℝ))) * maxGap I lam +
          ∑ i, lam i * expect I sel T (fun ω β => cap I T ω β (tauS I ystar L T ω β - 1) i) ≤
        bigLambda I lam *
          (3 * expect I sel T (fun ω β => (T : ℝ) - tauS I ystar L T ω β) + 4) := by sorry

end LPResolvingRM
