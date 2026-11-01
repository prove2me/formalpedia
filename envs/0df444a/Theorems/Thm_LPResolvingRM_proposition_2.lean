-- Prove2me | Theorems.Thm_LPResolvingRM_proposition_2
-- name    : LPResolvingRM.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:43:08.584412+00:00
-- url     : https://prove2.me/theorems/549fe436-0798-4405-addf-f198a27d5175
-- title:
--   Proposition 2 — misallocated orders before $\tau_S$ cost at most $2n\max_j|\mu_j-c_j^\top\lambda^*|/(1-e^{-2L^2})$
-- statement:
--   Under Assumptions 1 and 2, let $y^*$ be the optimal solution of (6), $(\lambda^*,\gamma^*)$ a dual optimal solution of (7), and $L\in(0,1]$ with $L\le\min_ib_i$ a stability radius. For every optimal solution rule for LP (5) and every $T\ge1$, the output of Algorithm 1 satisfies
--   $$\sum_{j\in\mathcal J^*}(\mu_j-c_j^\top\lambda^*)\,\mathbb E\big[n_j(\tau_S)-n^a_j(\tau_S)\big]+\sum_{j\in\mathcal J'}(c_j^\top\lambda^*-\mu_j)\,\mathbb E\big[n^a_j(\tau_S)\big]\le\frac{2n\max_j|\mu_j-c_j^\top\lambda^*|}{1-\exp(-2L^2)}.$$
--
--   The right-hand side does not depend on $T$: before $\tau_S$ the sampled LP shares the fluid LP's basis once the frequencies are accurate.
--
--   Differences from the source:
--   - encoding: (r_t, a_t) i.i.d. from P on the support {(µ_j, c_j)} → the type index j_t of each period i.i.d. with law p on Fin n, and (r_t, a_t) = (µ_{j_t}, c_{j_t}); reason: drawing the index gives the same law of (r_t, a_t)
--   - encoding: P takes the finite support {(µ_j, c_j)} → p_j > 0 for every j and ∑_j p_j = 1; reason: a support point has positive probability; p is a probability vector
--   - generalization: distinct support points (µ_j, c_j) → the pairs (µ_j, c_j) need not be distinct; the algorithm counts each index separately; reason: on distinct pairs this is the paper's model; the proofs never use distinctness
--   - encoding: E[·] over the arrivals and the algorithm's randomization → a finite sum over type sequences (Fin n)^T and coin sequences Bool^T weighted by the path probability; reason: all randomness is finite; same expectation
--   - encoding: periods t = 1, …, T, types 1..n, resources 1..m → Lean periods k = t − 1 : Fin T, types Fin n, resources Fin m; B_t is cap (t − 1), b_t is avgCap (t − 1); reason: index shift only
--   - reading: the optimal solution y*_t of LP (5) (tie-break unspecified) → every rule sel that maps (empirical frequencies, right-hand side ≥ 0) to an optimal solution of LP (5); reason: LP (5) may have several optima; the statement holds for every tie-breaking rule that is a function of the LP's data, including the paper's
--   - reading: Algorithm 1 line 3: set x₁ = 1 → x₁ = 1 when the constraint permits (c_{j₁} ≤ B₁), else 0; reason: no shorting is allowed (p.7); if B_{i,1} ≤ 1 for some i then τ = 0, otherwise c_{j₁} ≤ 1 < B₁, so the regret is unchanged
--   - encoding: λ*, the dual optimal solution of (7) → the λ-part of any dual optimal (λ, γ) of (7); reason: the dual optimum is unique when the primal optimum is nondegenerate (Assumption 2); same instances
--   - reading: L, the constant of Lemma 1 → any L with 0 < L ≤ 1, L ≤ min_i b_i and IsStabilityRadius L; reason: reading R1: the proofs use only Lemma 1's property and the WLOGs L ≤ 1 (p.26), 1 + L − b̲ ≤ 1 (p.40); the property is monotone in L, so the L of Lemma 1 can be shrunk to such an L
--   - reading: τ_S as displayed in §3.2 (p.11), with 'b_{i,t} − b_i > −L for some i ∈ I′' → the C.1 definition (p.35), b_{i,t} − b_i < −L, i.e. τ_S = min{t ≤ T : b_t ∉ 𝔅} ∪ {T + 1}; reason: the §3.2 sign is a typo; C.1 restates it with '< −L' and Appendix C uses that
--   - encoding: n_j(τ_S), n^a_j(τ_S) at τ_S = T + 1 → the counts over the whole horizon (no orders after T); reason: n_j(T + 1) = n_j(T) since no order arrives after T
--   - encoding: n(τ_S) → n_j(τ_S); reason: typo
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, Proposition 2, p.11 (general case, Appendix C, p.35)

import Definitions.Def_LPResolvingRM_DualOptimal
import Definitions.Def_LPResolvingRM_IsStabilityRadius
import Definitions.Def_LPResolvingRM_tauS

namespace LPResolvingRM

/-- **Proposition 2** (arXiv:2101.11092v3, p.11; general case, Appendix C, p.35): under
Assumptions 1 and 2, the output of Algorithm 1 satisfies

`∑_{j∈J*} (μ_j − c_jᵀλ*)·E[n_j(τ_S) − n^a_j(τ_S)] + ∑_{j∈J'} (c_jᵀλ* − μ_j)·E[n^a_j(τ_S)]
  ≤ 2n·max_j |μ_j − c_jᵀλ*| / (1 − exp(−2L²))`.

**Formalization Note.** `τ_S` is the C.1 stopping time (`LPResolvingRM.tauS`), for the unique
optimal solution `y*` of LP (6) and the stability radius `L` (reading R1: any `L ∈ (0, 1]` with
`L ≤ min_i b_i` satisfying Lemma 1's conclusion). The printed `n(τ_S)` is `n_j(τ_S)`. When
`τ_S = T + 1` the counts are those of the whole horizon. Every optimal rule `sel` for LP (5),
every dual optimal `(λ*, γ*)` and every `T ≥ 1`. -/
theorem proposition_2 {n m : ℕ} (I : Instance n m) (h1 : Assumption1 I) (h2 : Assumption2 I)
    (lam : Fin m → ℝ) (γ : Fin n → ℝ) (hdual : DualOptimal I lam γ)
    (ystar : Fin n → ℝ) (hystar : LPAllocRM.IsLPOptimal (normC I) I.b 1 (normMu I) ystar)
    (L : ℝ) (hL0 : 0 < L) (hL1 : L ≤ 1) (hLb : ∀ i, L ≤ I.b i)
    (hstab : IsStabilityRadius I L) (sel : Selector n m) (hsel : IsSelector I sel)
    (T : ℕ) (hT : 1 ≤ T) :
    ∑ j ∈ Jstar I lam, gap I lam j * expect I sel T (fun ω β =>
        (count ω (tauS I ystar L T ω β) j : ℝ) - acceptedCount I T ω β (tauS I ystar L T ω β) j) +
      ∑ j ∈ Jprime I lam, (-gap I lam j) * expect I sel T (fun ω β =>
        (acceptedCount I T ω β (tauS I ystar L T ω β) j : ℝ)) ≤
      2 * n * maxGap I lam / (1 - Real.exp (-2 * L ^ 2)) := by sorry

end LPResolvingRM
