-- Prove2me | Theorems.Thm_NoiseAssistedTransport_FCN_eq_A14
-- name    : NoiseAssistedTransport.FCN.eq_A14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:14.045656+00:00
-- url     : https://prove2.me/theorems/b9f53abe-12d1-498a-a7bd-02516b81dcfb
-- title:
--   Eq. (A14), p. 13 — closed form of ρ_NN(t) for the noiseless FCN
-- statement:
--   Consider the noiseless fully connected network of Appendix A.2 ($\Gamma = 0$, $\gamma = 0$, zero site energies) with $N \ge 3$ sites, hopping $J \ne 0$, the sink coupled to site $N$ with rate $\Gamma_{N+1} > 0$, and the initial state $|1\rangle\langle 1|$. Put
--
--   $$S = \sqrt{(\Gamma_{N+1}^2 + J^2N^2)^2 - 16(N-1)\Gamma_{N+1}^2J^2}, \qquad \Delta_\pm^2 = \tfrac12(\Gamma_{N+1}^2 - J^2N^2) \pm \tfrac12 S \quad \text{(A13)}.$$
--
--   Then for every $t \ge 0$ the population of the sink-coupled site is
--
--   $$\rho_{NN}(t) = \frac{2J^2e^{-\Gamma_{N+1}t}\,[\cosh(\Delta_+t) - \cosh(\Delta_-t)]}{S}.$$
--
--   Integrating this closed form gives $p_{\rm sink}(t)$ through (A15), and its limit gives $p_{\rm sink}(\infty) = 1/(N-1)$.
--
--   **Formalization Note** $\Delta_-^2$ (and possibly $\Delta_+^2$) is negative in general, so $\Delta_\pm$ is the complex principal square root of the real number $\Delta_\pm^2$ and $\cosh$ is the complex hyperbolic cosine; since $\cosh$ is even, the choice of root does not matter. The identity is an equality of complex numbers. For $N \ge 3$, $J \ne 0$ and $\Gamma_{N+1} \ne 0$ the radicand of $S$ is positive, so $S > 0$.
-- source:
--   Caruso et al., Highly efficient energy excitation transfer in light-harvesting complexes, arXiv:0901.4454v2, p. 13, Appendix A.2, Eqs. (A13)–(A14)

import Mathlib
import Definitions.Def_NoiseAssistedTransport_FCN_Model
open scoped Matrix
open Fin.NatCast

namespace NoiseAssistedTransport.FCN

/-- (A13)–(A14), p. 13: closed form of `ρ_NN(t)` for the noiseless FCN. `Δ_±` are complex square
roots of the real numbers `Δ²_±`; `cosh` is even, so the branch does not matter. -/
theorem eq_A14 (N : ℕ) (hN : 3 ≤ N) (J Γs : ℝ) (hJ : J ≠ 0) (hΓs : 0 < Γs) (t : ℝ)
    (ht : 0 ≤ t) :
    let S : ℝ := Real.sqrt ((Γs ^ 2 + J ^ 2 * (N : ℝ) ^ 2) ^ 2
      - 16 * ((N : ℝ) - 1) * Γs ^ 2 * J ^ 2)
    let Δp : ℂ := (((Γs ^ 2 - J ^ 2 * (N : ℝ) ^ 2) / 2 + S / 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ)
    let Δm : ℂ := (((Γs ^ 2 - J ^ 2 * (N : ℝ) ^ 2) / 2 - S / 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ)
    fcnEvolve N J 0 Γs t ((N : ℕ) : Fin (N + 2)) ((N : ℕ) : Fin (N + 2)) =
      ((2 * J ^ 2 * Real.exp (-(Γs * t)) : ℝ) : ℂ)
        * (Complex.cosh (Δp * (t : ℂ)) - Complex.cosh (Δm * (t : ℂ))) / (S : ℂ) := by sorry

end NoiseAssistedTransport.FCN
