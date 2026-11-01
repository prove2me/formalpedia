-- Prove2me | Theorems.Thm_LPResolvingRM_corollary_1
-- name    : LPResolvingRM.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:42:58.507125+00:00
-- url     : https://prove2.me/theorems/f613c844-b635-4a73-99c7-7653075aed33
-- title:
--   Corollary 1 — the regret decomposition at a stopping time $\tau'\le\tau$
-- statement:
--   Under Assumptions 1 and 2, for every dual optimal $(\lambda^*,\gamma^*)$, every optimal solution rule for LP (5), every horizon $T$ and every stopping time $\tau'$ adapted to $(B_t)$ with $\tau'\le\tau$ on every sample path,
--   $$\mathrm{Reg}^\pi_T\le\sum_{j\in\mathcal J^*}(\mu_j-c_j^\top\lambda^*)\,\mathbb E\big[n_j(\tau')-n^a_j(\tau')\big]+\sum_{j\in\mathcal J'}(c_j^\top\lambda^*-\mu_j)\,\mathbb E\big[n^a_j(\tau')\big]+(T-\mathbb E[\tau'])\max_{j\in[n]}|\mu_j-c_j^\top\lambda^*|+\lambda^{*\top}\,\mathbb E[B_{\tau'+1}].$$
--
--   The extra term $T-\mathbb E[\tau']$ measures how far $\tau'$ is from the end of the horizon; the analysis applies it with $\tau'=\tau_S$.
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
--   - reading: E[B_{τ′}] → E[B_{τ′+1}]; reason: as B_τ in Proposition 1 (reading R2), from which the corollary is derived; B_{τ′+1} ≤ B_{τ′}, so this is the stronger form
--   - encoding: τ′ ≤ τ almost surely → τ′ ≤ τ on every sample path; reason: the sample space is finite
--   - encoding: Corollary 1 states no assumption → Assumptions 1 and 2; reason: it is derived from Proposition 1, which assumes them
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, Corollary 1, pp.10–11 (proof A.2)

import Definitions.Def_LPResolvingRM_DualOptimal
import Definitions.Def_LPResolvingRM_tauS

namespace LPResolvingRM

/-- **Corollary 1** (arXiv:2101.11092v3, pp.10–11): under Assumptions 1 and 2 (as for
Proposition 1),

`Reg^π_T ≤ ∑_{j∈J*} (μ_j − c_jᵀλ*)·E[n_j(τ') − n^a_j(τ')] + ∑_{j∈J'} (c_jᵀλ* − μ_j)·E[n^a_j(τ')]
  + (T − E[τ'])·max_{j∈[n]} |μ_j − c_jᵀλ*| + λ*ᵀ·E[B_{τ'}]`,

"where τ′ is a stopping time adapted to the process B_t's and τ′ ≤ τ almost surely".

**Formalization Note.** `B_{τ'}` is read as `B_{τ'+1}` (`cap … τ'`), as `B_τ` in Proposition 1
(reading R2); since `B_{τ'+1} ≤ B_{τ'}` this is the stronger form. "Almost surely" is "on every
sample path". -/
theorem corollary_1 {n m : ℕ} (I : Instance n m) (h1 : Assumption1 I) (h2 : Assumption2 I)
    (lam : Fin m → ℝ) (γ : Fin n → ℝ) (hdual : DualOptimal I lam γ)
    (sel : Selector n m) (hsel : IsSelector I sel) (T : ℕ)
    (τ' : (Fin T → Fin n) → (Fin T → Bool) → ℕ) (hstop : IsBStoppingTime I T τ')
    (hle : ∀ ω β, τ' ω β ≤ tau I T ω β) :
    regret I sel T ≤
      ∑ j ∈ Jstar I lam, gap I lam j * expect I sel T (fun ω β =>
          (count ω (τ' ω β) j : ℝ) - acceptedCount I T ω β (τ' ω β) j) +
      ∑ j ∈ Jprime I lam, (-gap I lam j) * expect I sel T (fun ω β =>
          (acceptedCount I T ω β (τ' ω β) j : ℝ)) +
      ((T : ℝ) - expect I sel T (fun ω β => (τ' ω β : ℝ))) * maxGap I lam +
      ∑ i, lam i * expect I sel T (fun ω β => cap I T ω β (τ' ω β) i) := by sorry

end LPResolvingRM
