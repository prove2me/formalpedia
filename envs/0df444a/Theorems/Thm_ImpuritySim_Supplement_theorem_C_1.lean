-- Prove2me | Theorems.Thm_ImpuritySim_Supplement_theorem_C_1
-- name    : ImpuritySim.Supplement.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:34:14.67095+00:00
-- url     : https://prove2.me/theorems/b01098c8-f05e-418f-9cbc-87da56eacb7d
-- title:
--   Theorem C.1 — absolute trace-norm convergence of $\sum_r D_r=e^{-\beta H}$ and the truncation bounds (C.4)
-- statement:
--   Let $H=H_{\mathrm{ref}}+V$ act on a finite-dimensional Hilbert space of positive dimension, with $H_{\mathrm{ref}}$ Hermitian and $V=\sum_{a=1}^Rv_aU_a$ Hermitian, $v_a\in\mathbb R$, $\|U_a\|\le1$, and $W=\sum_a|v_a|$ (C.1). Let $\beta\ge0$, and let $D_r$ and $G_K=\sum_{r=0}^KD_r$ be the terms and truncations of the imaginary-time interaction-picture expansion.
--
--   1. The expansion $e^{-\beta H}=\sum_{r=0}^\infty D_r$ converges absolutely in trace norm: $\sum_r\|D_r\|_1<\infty$ and $\sum_rD_r=e^{-\beta H}$.
--   2. Let $O$ be Hermitian with $\|O\|\le1$, and write $Z_K=\operatorname{Re}\operatorname{Tr}G_K$, $N_K=\operatorname{Re}\operatorname{Tr}(OG_K)$, $\mu_K=N_K/Z_K$, $Z=\operatorname{Tr}e^{-\beta H}$, $\rho^{(\beta)}=e^{-\beta H}/Z$. For every $\epsilon\in(0,1)$ and every natural number $K\ge4e\beta W+\log_2(16/\epsilon)$,
--   $$Z_K\ge\frac{15}{16}Z>0,\qquad|Z_K-Z|\le\frac\epsilon{16}Z,\qquad\bigl|\mu_K-\operatorname{Tr}(O\rho^{(\beta)})\bigr|\le\frac{2\epsilon}{15},\qquad|\mu_K|<\frac65.\qquad(C.4)$$
--
--   This is the truncation step of continuous-time quantum Monte Carlo: an order $K=O(\beta W+\log(1/\epsilon))$ suffices for the truncated expansion to estimate both the partition function and a bounded thermal expectation.
--
--   **Formalization Note** $\|\cdot\|$ is the spectral norm and $\|\cdot\|_1$ the trace norm (sum of singular values). The integrals defining $D_r$ are entrywise Lebesgue integrals over the ordered simplex.
--
--   Differences from the source:
--   - reading: "set K = O(βW + log(1/ϵ))" → every natural K ≥ 4eβW + log₂(16/ϵ); reason: this is the threshold the proof chooses (p.60, "Choose K ≥ 4eβW + log₂ 16/ϵ"), and every K above it is covered
--   - reading: H = H_ref + V a Hamiltonian (C.1) → H_ref and V Hermitian; reason: H is a Hamiltonian and the decomposition is into a reference Hamiltonian and a perturbation; the proof uses H_ref − WI ≤ H ≤ H_ref + WI and Z_ref = Tr e^{−βH_ref} > 0
--   - generalization: an inverse temperature β > 0 (§6, App. C) → every β ≥ 0; reason: at β = 0 the claim also holds (D_r = 0 for r ≥ 1); for β > 0 it is the source's
--   - encoding: a finite-dimensional Hilbert space → a nonempty finite index type ι; reason: a Hilbert space with a basis, of positive dimension (Z > 0)
--   - encoding: the matrix-valued integral over Ω_r(β) → the entrywise Lebesgue integral on ℝ^r; reason: the integrand is continuous on a compact set, so it equals the Bochner integral
--   - encoding: Z = Tr(e^{−βH}) and Tr(Oρ^(β)) → the real part of Tr e^{−βH}, and |µ_K − Tr(Oρ^(β))| as a complex modulus; reason: both traces are real for Hermitian H and O
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Theorem C.1, Eq. (C.4), p.60; (C.1), p.59; proof pp.60–61

import Mathlib
import Definitions.Def_ImpuritySim_Supplement_Interaction
import Definitions.Def_ImpuritySim_Fermion
import Definitions.Def_WolfAreaLaw_thermalState
import Definitions.Def_WildeQIT_traceNorm

namespace ImpuritySim.Supplement

/-- **Theorem C.1 (Truncating the interaction-picture expansion)**, p.60, of J. Jiang, N. Ju,
O. Parekh, C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation of quantum
impurity models*, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Eq. (C.4), with the
setting (C.1), p.59, and `Ω_r(β)`, `V_I`, `D_r`, `G_K` of p.60.

Let `H = H_ref + V` on a nonempty finite-dimensional space, `H_ref` Hermitian,
`V = Σ_{a=1}^R v_a U_a` Hermitian with `v_a ∈ ℝ` and `‖U_a‖ ≤ 1`, `W = Σ_a |v_a|`, and `β ≥ 0`.
1. The expansion `e^{−βH} = Σ_{r=0}^∞ D_r` converges absolutely in trace norm:
   `Σ_r ‖D_r‖_1 < ∞` and `Σ_r D_r = e^{−βH}`.
2. For every Hermitian `O` with `‖O‖ ≤ 1`, every `ϵ ∈ (0, 1)` and every natural
   `K ≥ 4eβW + log₂(16/ϵ)`, with `Z_K = Re Tr G_K`, `N_K = Re Tr(O G_K)`, `μ_K = N_K/Z_K`,
   `Z = Tr e^{−βH}`:
   `Z_K ≥ (15/16) Z > 0`, `|Z_K − Z| ≤ (ϵ/16) Z`, `|μ_K − Tr(O ρ^(β))| ≤ 2ϵ/15`, `|μ_K| < 6/5`.

**Formalization Note.**
* "Set `K = O(βW + log(1/ϵ))`" is read as every natural `K` at or above the threshold
  `4eβW + log₂(16/ϵ)` the proof itself chooses (p.60).
* `H` is a Hamiltonian, so `H_ref` and `V` are taken Hermitian; the index type is nonempty (a
  Hilbert space of positive dimension).
* The page works at an inverse temperature `β > 0`; the statement is taken for every `β ≥ 0`
  (at `β = 0` it holds with `D_r = 0` for `r ≥ 1`).
* `‖·‖` is the spectral norm (`ImpuritySim.specNorm`), `‖·‖_1` the trace norm
  (`WildeQIT.traceNorm`, `Tr √(X†X)`, the sum of singular values). `Z` is the real part of the
  trace of `e^{−βH}` (which is real and positive); `Tr(Oρ^(β))` is compared as a complex number. -/
theorem theorem_C_1 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Href : Matrix ι ι ℂ) (hHref : Href.IsHermitian) {R : ℕ} (v : Fin R → ℝ)
    (U : Fin R → Matrix ι ι ℂ) (hU : ∀ a, specNorm (U a) ≤ 1) (hV : (Vop v U).IsHermitian)
    (β : ℝ) (hβ : 0 ≤ β) :
    (Summable (fun r => WildeQIT.traceNorm (Dterm Href (Vop v U) β r)) ∧
      HasSum (fun r => Dterm Href (Vop v U) β r)
        (NormedSpace.exp (-(β : ℂ) • (Href + Vop v U)))) ∧
    ∀ O : Matrix ι ι ℂ, O.IsHermitian → specNorm O ≤ 1 →
      ∀ ϵ : ℝ, 0 < ϵ → ϵ < 1 →
        ∀ K : ℕ, 4 * Real.exp 1 * β * Wsum v + Real.logb 2 (16 / ϵ) ≤ (K : ℝ) →
          15 / 16 * (NormedSpace.exp (-(β : ℂ) • (Href + Vop v U))).trace.re ≤
              (GK Href (Vop v U) β K).trace.re ∧
            0 < 15 / 16 * (NormedSpace.exp (-(β : ℂ) • (Href + Vop v U))).trace.re ∧
            |(GK Href (Vop v U) β K).trace.re -
                (NormedSpace.exp (-(β : ℂ) • (Href + Vop v U))).trace.re| ≤
              ϵ / 16 * (NormedSpace.exp (-(β : ℂ) • (Href + Vop v U))).trace.re ∧
            ‖((((O * GK Href (Vop v U) β K).trace.re / (GK Href (Vop v U) β K).trace.re : ℝ)) : ℂ) -
                (O * WolfAreaLaw.thermalState β (Href + Vop v U)).trace‖ ≤ 2 * ϵ / 15 ∧
            |(O * GK Href (Vop v U) β K).trace.re / (GK Href (Vop v U) β K).trace.re| < 6 / 5 := by sorry

end ImpuritySim.Supplement
