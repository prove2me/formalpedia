-- Prove2me | Theorems.Thm_NoiseAssistedTransport_FCN_population_sum_rule
-- name    : NoiseAssistedTransport.FCN.population_sum_rule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:12.888445+00:00
-- url     : https://prove2.me/theorems/e74fdb85-999b-41a0-b2fd-f2820c3abf36
-- title:
--   Eq. (A7), p. 12 — population sum rule 1 = Tr ρ + ρ_00 + p_sink
-- statement:
--   Consider the fully connected network of $N$ sites with arbitrary real site energies $\omega_j$, dissipation rates $\Gamma_j$, dephasing rates $\gamma_j$, hopping $J$ and sink rate $\Gamma_{N+1}$, with the sink coupled to a site $k$, $1 \le k \le N$, and started in $|1\rangle\langle 1|$. Let $\rho(t)$ be its state and $p_{\rm sink}(t) = 2\Gamma_{N+1}\int_0^t\rho_{kk}(t')\,dt'$ its sink population. Then for every time $t$
--
--   $$1 = \operatorname{Tr}\rho(t) + \rho_{00}(t) + p_{\rm sink}(t), \qquad \operatorname{Tr}\rho(t) = \sum_{j=1}^N \rho_{jj}(t).$$
--
--   Here $\operatorname{Tr}\rho$ is the population held in the network, $\rho_{00}$ the population lost to the environment, and $p_{\rm sink}$ the population transferred to the sink: none of the initial excitation is lost overall. The identity is what converts the network trace in the equations of motion into the closed collective system of Appendix A.1, and it ties the sink entry of $\rho$ to the integral $p_{\rm sink}$.
--
--   **Formalization Note** The paper states (A7) in the uniform setting of Appendix A.1 but says that it "must always hold"; the statement is made for arbitrary site-dependent real parameters, which contains the uniform case. Each population is the real part of the corresponding diagonal entry.
-- source:
--   Caruso et al., Highly efficient energy excitation transfer in light-harvesting complexes, arXiv:0901.4454v2, p. 12, Appendix A.1, Eq. (A7); cf. p. 13, Eq. (A19)

import Mathlib
import Definitions.Def_NoiseAssistedTransport_FCN_Model
open scoped Matrix
open Fin.NatCast

namespace NoiseAssistedTransport.FCN

/-- (A7), p. 12: `1 = Tr ρ + ρ_00 + p_sink`, with `Tr ρ = Σ_{j=1}^{N} ρ_jj` the network population. -/
theorem population_sum_rule (N : ℕ) (ω Γ γ : ℕ → ℝ) (J Γs : ℝ) (k : ℕ) (hk1 : 1 ≤ k)
    (hkN : k ≤ N) (t : ℝ) :
    1 = ∑ j ∈ Finset.Icc 1 N,
          (evolve N ω Γ γ J Γs k (initState N) t ((j : ℕ) : Fin (N + 2)) ((j : ℕ) : Fin (N + 2))).re
        + (evolve N ω Γ γ J Γs k (initState N) t 0 0).re
        + sinkPop N ω Γ γ J Γs k (initState N) t := by sorry

end NoiseAssistedTransport.FCN
