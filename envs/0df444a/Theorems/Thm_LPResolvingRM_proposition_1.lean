-- Prove2me | Theorems.Thm_LPResolvingRM_proposition_1
-- name    : LPResolvingRM.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:42:29.893834+00:00
-- url     : https://prove2.me/theorems/1104a9fd-b4a3-4a3a-b51a-592e9f17c55f
-- title:
--   Proposition 1 — regret decomposition by the dual price
-- statement:
--   Under Assumptions 1 and 2, for every dual optimal $(\lambda^*,\gamma^*)$ of (7), every optimal solution rule for LP (5) and every horizon $T$,
--   $$\mathrm{Reg}^\pi_T=\sum_{j\in\mathcal J^*}(\mu_j-c_j^\top\lambda^*)\,\mathbb E\big[n_j(T)-n^a_j(\tau)\big]+\sum_{j\in\mathcal J'}(c_j^\top\lambda^*-\mu_j)\,\mathbb E\big[n^a_j(\tau)\big]+\lambda^{*\top}\,\mathbb E[B_{\tau+1}],$$
--   where $n_j(t)$ and $n^a_j(t)$ are the numbers of arrived and of accepted type-$j$ orders up to time $t$ (inclusive), and $B_{\tau+1}=B-\sum_{t\le\tau}a_tx_t$ is the capacity remaining when the algorithm terminates.
--
--   The first two terms count wrongly accepted or rejected orders; the last penalizes leftover resources.
--
--   Differences from the source:
--   - encoding: (r_t, a_t) i.i.d. from P on the support {(µ_j, c_j)} → the type index j_t of each period i.i.d. with law p on Fin n, and (r_t, a_t) = (µ_{j_t}, c_{j_t}); reason: drawing the index gives the same law of (r_t, a_t)
--   - encoding: P takes the finite support {(µ_j, c_j)} → p_j > 0 for every j and ∑_j p_j = 1; reason: a support point has positive probability; p is a probability vector
--   - generalization: distinct support points (µ_j, c_j) → the pairs (µ_j, c_j) need not be distinct; the algorithm counts each index separately; reason: on distinct pairs this is the paper's model; the proofs never use distinctness
--   - encoding: E[·] over the arrivals and the algorithm's randomization → a finite sum over type sequences (Fin n)^T and coin sequences Bool^T weighted by the path probability; reason: all randomness is finite; same expectation
--   - encoding: periods t = 1, …, T, types 1..n, resources 1..m → Lean periods k = t − 1 : Fin T, types Fin n, resources Fin m; B_t is cap (t − 1), b_t is avgCap (t − 1); reason: index shift only
--   - reading: the optimal solution y*_t of LP (5) (tie-break unspecified) → every rule sel that maps (empirical frequencies, right-hand side ≥ 0) to an optimal solution of LP (5); reason: LP (5) may have several optima; the statement holds for every tie-breaking rule that is a function of the LP's data, including the paper's
--   - reading: Algorithm 1 line 3: set x₁ = 1 → x₁ = 1 when the constraint permits (c_{j₁} ≤ B₁), else 0; reason: no shorting is allowed (p.7); if B_{i,1} ≤ 1 for some i then τ = 0, otherwise c_{j₁} ≤ 1 < B₁, so the regret is unchanged
--   - reading: τ := min{t : B_{i,t} ≤ 1 for some i} − 1 → t ranges over 1, …, T + 1 and τ := T when no such t exists; reason: reading R4: the algorithm runs to the end; the only reading under which the regret is defined on every path
--   - encoding: λ*, the dual optimal solution of (7) → the λ-part of any dual optimal (λ, γ) of (7); reason: the dual optimum is unique when the primal optimum is nondegenerate (Assumption 2); same instances
--   - reading: E[B_τ], 'the remaining resource vector when the algorithm terminates' → E[B_{τ+1}], the capacity after period τ; reason: reading R2: with the beginning-of-period B_τ the identity is false (n = m = 1, µ = c = p = 1, b = ½, T = 4: regret 1, λ*B_τ = 2); the proof (A.1, p.23) computes λ*ᵀ(B − ∑_{t≤τ} a_t x_t)
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, Proposition 1, p.10 (proof A.1, p.23)

import Definitions.Def_LPResolvingRM_DualOptimal
import Definitions.Def_LPResolvingRM_regret

namespace LPResolvingRM

/-- **Proposition 1 (regret decomposition)** (arXiv:2101.11092v3, p.10): under Assumptions 1
and 2,

`Reg^π_T = ∑_{j∈J*} (μ_j − c_jᵀλ*)·E[n_j(T) − n^a_j(τ)] + ∑_{j∈J'} (c_jᵀλ* − μ_j)·E[n^a_j(τ)]
  + λ*ᵀ·E[B_τ]`,

where `n^a_j(t)` is the number of accepted type-`j` orders up to time `t` (inclusive) and
`n_j(t)` the number of type-`j` orders up to time `t`.

**Formalization Note.** Reading R2: `B_τ` is "the remaining resource vector when the algorithm
terminates" (p.10), `B_{τ+1} = B − ∑_{t≤τ} a_t x_t` (the proof, A.1, p.23), i.e.
`cap … (tau …)`; with the beginning-of-period `B_τ` the identity is false (`n = m = 1`,
`μ = c = p = 1`, `b = ½`, `T = 4`). Stated for every dual optimal `(λ*, γ*)`, every optimal
rule `sel` for LP (5) and every horizon `T`. -/
theorem proposition_1 {n m : ℕ} (I : Instance n m) (h1 : Assumption1 I) (h2 : Assumption2 I)
    (lam : Fin m → ℝ) (γ : Fin n → ℝ) (hdual : DualOptimal I lam γ)
    (sel : Selector n m) (hsel : IsSelector I sel) (T : ℕ) :
    regret I sel T =
      ∑ j ∈ Jstar I lam, gap I lam j * expect I sel T (fun ω β =>
          (count ω T j : ℝ) - acceptedCount I T ω β (tau I T ω β) j) +
      ∑ j ∈ Jprime I lam, (-gap I lam j) * expect I sel T (fun ω β =>
          (acceptedCount I T ω β (tau I T ω β) j : ℝ)) +
      ∑ i, lam i * expect I sel T (fun ω β => cap I T ω β (tau I T ω β) i) := by sorry

end LPResolvingRM
