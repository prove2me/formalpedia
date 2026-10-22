-- Prove2me | Theorems.Thm_NoiseAssistedTransport_FCN_noise_assisted_transport
-- name    : NoiseAssistedTransport.FCN.noise_assisted_transport
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:14.607467+00:00
-- url     : https://prove2.me/theorems/300f07ac-3a39-4b97-bbd7-f0039d518f5f
-- title:
--   Eq. (5), p. 4 and §II.C, p. 5 / (A30), p. 14 — FCN sink population tends to 1/(N−1) without noise and to 1 under any uniform dephasing γ > 0
-- statement:
--   Consider the fully connected network of §II.A with $N \ge 2$ sites: every pair of distinct sites coupled with hopping $J \ne 0$, zero site energies, no dissipation, the sink attached to site $N$ with rate $\Gamma_{N+1} > 0$, and a single excitation initially on site 1. Let $p_{\rm sink}(t) = 2\Gamma_{N+1}\int_0^t\rho_{NN}(t')\,dt'$ be the population transferred to the sink by time $t$, when every site dephases at the same rate $\gamma \ge 0$.
--
--   1. Without dephasing ($\gamma = 0$),
--   $$\lim_{t\to\infty} p_{\rm sink}(t) = \frac{1}{N-1}.$$
--   2. With uniform local dephasing at any rate $\gamma > 0$,
--   $$\lim_{t\to\infty} p_{\rm sink}(t) = 1.$$
--
--   This is the paper's demonstration of **noise-assisted transport**: in the coherent network destructive interference traps a fraction $\frac{N-2}{N-1}$ of the excitation forever, and any amount of local dephasing destroys the invariant subspace and lets the whole excitation reach the sink.
--
--   **Formalization Note** The hypotheses are necessary: with $J = 0$ or $\Gamma_{N+1} = 0$ nothing reaches the sink, and $N \ge 2$ makes site 1 differ from the sink-coupled site $N$ (for $N = 1$, $1/(N-1)$ is undefined). For $N = 2$ the first limit is $1$. Clause 2 is stated for a uniform rate $\gamma_j = \gamma$, the case the paper solves exactly; it is quantified over every $\gamma > 0$ ("for any finite $\gamma$").
-- source:
--   Caruso et al., Highly efficient energy excitation transfer in light-harvesting complexes, arXiv:0901.4454v2, p. 4, §II.A, Eq. (5); pp. 5–6, §II.C; p. 13, Appendix A.2 (p_sink(∞) = 1/(N−1)); p. 14, Appendix A.3, Eq. (A30)

import Mathlib
import Definitions.Def_NoiseAssistedTransport_FCN_Model
open scoped Matrix
open Fin.NatCast

namespace NoiseAssistedTransport.FCN

/-- Eq. (5), p. 4, and §II.C, p. 5 / (A30), p. 14: in the FCN (`ω_j = Γ_j = 0`, sink at site `N`,
start `|1⟩⟨1|`) the sink population tends to `1/(N − 1)` without dephasing and to `1` under any
uniform dephasing rate `γ > 0`. -/
theorem noise_assisted_transport (N : ℕ) (hN : 2 ≤ N) (J Γs : ℝ) (hJ : J ≠ 0) (hΓs : 0 < Γs) :
    Filter.Tendsto (fcnSinkPop N J 0 Γs) Filter.atTop (nhds (1 / ((N : ℝ) - 1))) ∧
    ∀ γ : ℝ, 0 < γ → Filter.Tendsto (fcnSinkPop N J γ Γs) Filter.atTop (nhds 1) := by sorry

end NoiseAssistedTransport.FCN
