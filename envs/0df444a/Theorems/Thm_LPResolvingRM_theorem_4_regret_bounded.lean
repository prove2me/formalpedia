-- Prove2me | Theorems.Thm_LPResolvingRM_theorem_4_regret_bounded
-- name    : LPResolvingRM.theorem_4_regret_bounded
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:42:20.122029+00:00
-- url     : https://prove2.me/theorems/6ea9a373-87c5-45dd-a0be-764e48f95c46
-- title:
--   Theorem 4 — horizon-independent regret of the re-solving algorithm under nondegeneracy (corrected: $\|\lambda^*\|_1\to\max\{\|\lambda^*\|_1,\max_j|\mu_j-c_j^\top\lambda^*|\}$)
-- statement:
--   Let the instance satisfy Assumptions 1 and 2, let $(\lambda^*,\gamma^*)$ be a dual optimal solution of (7), and let $L$ be a stability radius (the property of Lemma 1) with $0<L\le1$ and $L\le\min_ib_i$. Put
--   $$\Lambda=\max\Big\{\|\lambda^*\|_1,\ \max_{j\in[n]}|\mu_j-c_j^\top\lambda^*|\Big\}.$$
--   Then there is a function $g$ with $g(T)\to0$ as $T\to\infty$ such that, for every rule choosing an optimal solution of the sampled LP (5) and every horizon $T\ge1$, the regret of Algorithm 1 satisfies
--   $$\mathrm{Reg}^\pi_T\le\frac{(48m+4n+12)\cdot\Lambda}{L^2}+g(T).$$
--
--   The bound does not grow with the horizon $T$: frequent re-solving with empirical frequencies loses only a constant compared with the fluid benchmark when the fluid LP is nondegenerate.
--
--   Differences from the source:
--   - correction: (48m + 4n + 12)·‖λ*‖₁/L² + o(1) → (48m + 4n + 12)·Λ/L² + g(T), Λ = max{‖λ*‖₁, max_j |µ_j − c_jᵀλ*|}; reason: the printed bound is false: m = 1, n = 2, (µ, c) = (1, 1), (1, 0), p = (½, ½), b = 0.6 satisfy Assumptions 1–2 with λ* = 0, yet Reg_T ≥ 0.1 for every T ≥ 4 (a type-1 order at t = 2 after one at t = 1 is rejected with probability > 0.4); the proof (p.41, via p.25) uses max_j|µ_j − c_jᵀλ*| ≤ ‖λ*‖₁, and its chain closes with Λ
--   - encoding: o(1) → ∃ g : ℕ → ℝ with g → 0, the same g for every LP solution rule and every T ≥ 1; reason: the o(1) term of the proof (p.41) is explicit and does not depend on the tie-breaking rule
--   - encoding: (r_t, a_t) i.i.d. from P on the support {(µ_j, c_j)} → the type index j_t of each period i.i.d. with law p on Fin n, and (r_t, a_t) = (µ_{j_t}, c_{j_t}); reason: drawing the index gives the same law of (r_t, a_t)
--   - encoding: P takes the finite support {(µ_j, c_j)} → p_j > 0 for every j and ∑_j p_j = 1; reason: a support point has positive probability; p is a probability vector
--   - generalization: distinct support points (µ_j, c_j) → the pairs (µ_j, c_j) need not be distinct; the algorithm counts each index separately; reason: on distinct pairs this is the paper's model; the proofs never use distinctness
--   - encoding: E[·] over the arrivals and the algorithm's randomization → a finite sum over type sequences (Fin n)^T and coin sequences Bool^T weighted by the path probability; reason: all randomness is finite; same expectation
--   - encoding: periods t = 1, …, T, types 1..n, resources 1..m → Lean periods k = t − 1 : Fin T, types Fin n, resources Fin m; B_t is cap (t − 1), b_t is avgCap (t − 1); reason: index shift only
--   - reading: the optimal solution y*_t of LP (5) (tie-break unspecified) → every rule sel that maps (empirical frequencies, right-hand side ≥ 0) to an optimal solution of LP (5); reason: LP (5) may have several optima; the statement holds for every tie-breaking rule that is a function of the LP's data, including the paper's
--   - reading: Algorithm 1 line 3: set x₁ = 1 → x₁ = 1 when the constraint permits (c_{j₁} ≤ B₁), else 0; reason: no shorting is allowed (p.7); if B_{i,1} ≤ 1 for some i then τ = 0, otherwise c_{j₁} ≤ 1 < B₁, so the regret is unchanged
--   - reading: τ := min{t : B_{i,t} ≤ 1 for some i} − 1 → t ranges over 1, …, T + 1 and τ := T when no such t exists; reason: reading R4: the algorithm runs to the end; the only reading under which the regret is defined on every path
--   - encoding: λ*, the dual optimal solution of (7) → the λ-part of any dual optimal (λ, γ) of (7); reason: the dual optimum is unique when the primal optimum is nondegenerate (Assumption 2); same instances
--   - reading: L, the constant of Lemma 1 → any L with 0 < L ≤ 1, L ≤ min_i b_i and IsStabilityRadius L; reason: reading R1: the proofs use only Lemma 1's property and the WLOGs L ≤ 1 (p.26), 1 + L − b̲ ≤ 1 (p.40); the property is monotone in L, so the L of Lemma 1 can be shrunk to such an L
--   - reading: LP (8) shares the same optimal basis and set of binding constraints with LP (6) → LP (8) has a unique optimal solution with the same nonzero coordinates among (y, s, z) and the same binding set; reason: E.2 (p.50): 'the optimal solution to LP (8) is unique and it shares the same optimal basis and binding/non-binding structure'
--   - reading: ‖Ĉ − C‖_∞ for a matrix → the entrywise maximum max_{i,j} |Ĉ_{ij} − C_{ij}|; reason: reading R3: the proof of Proposition 2 (p.24) and E.2 (p.50) bound it entrywise
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, Theorem 4, p.37 (proof C.4, pp.40–41)

import Definitions.Def_LPResolvingRM_DualOptimal
import Definitions.Def_LPResolvingRM_IsStabilityRadius
import Definitions.Def_LPResolvingRM_regret

open Filter Topology

namespace LPResolvingRM

/-- **Theorem 4 (corrected constant)** (Chen, Li, Ye, *An Improved Analysis of LP-based Control
for Revenue Management*, arXiv:2101.11092v3, Appendix C, p.37): "Under Assumption 1 and 2,
Algorithm 1 give a regret in the order of Reg^π_T ≤ (48m + 4n + 12)·‖λ∗‖₁/L² + o(1)."

Stated with `Λ := max{‖λ*‖₁, max_j |μ_j − c_jᵀλ*|}` in place of `‖λ*‖₁`: for every instance
satisfying Assumptions 1 and 2, every dual optimal solution `(λ*, γ*)` of (7) and every stability
radius `L ∈ (0, 1]` with `L ≤ min_i b_i`, there is a function `g → 0` such that for every
optimal-solution rule `sel` for the sampled LP (5) and every horizon `T ≥ 1`,
`Reg_T ≤ (48m + 4n + 12)·Λ/L² + g(T)`.

**Formalization Note.** The printed constant is false (m = 1, n = 2, `(μ, c) = (1, 1), (1, 0)`,
`p = (½, ½)`, `b = 0.6`: `λ* = 0` but `Reg_T ≥ 0.1` for every `T ≥ 4`); the proof (p.41) bounds
`max_j|μ_j − c_jᵀλ*|` and `‖λ*‖₁` separately, which `Λ` dominates. `L` is any admissible
radius (reading R1, p.26 "we can assume L ≤ 1", p.40 "1 + L − b̲ ≤ 1"). The `o(1)` is an
explicit `g` with `g(T) → 0` that does not depend on `sel` (as the explicit term on p.41).
Regret, `τ` and the law of the run are as in `LPResolvingRM.regret`. -/
theorem theorem_4_regret_bounded {n m : ℕ} (I : Instance n m) (h1 : Assumption1 I)
    (h2 : Assumption2 I) (lam : Fin m → ℝ) (γ : Fin n → ℝ) (hdual : DualOptimal I lam γ)
    (L : ℝ) (hL0 : 0 < L) (hL1 : L ≤ 1) (hLb : ∀ i, L ≤ I.b i)
    (hstab : IsStabilityRadius I L) :
    ∃ g : ℕ → ℝ, Tendsto g atTop (𝓝 0) ∧
      ∀ sel : Selector n m, IsSelector I sel → ∀ T : ℕ, 1 ≤ T →
        regret I sel T ≤ (48 * m + 4 * n + 12) * bigLambda I lam / L ^ 2 + g T := by sorry

end LPResolvingRM
