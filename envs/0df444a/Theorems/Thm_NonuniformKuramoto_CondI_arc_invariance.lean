-- Prove2me | Theorems.Thm_NonuniformKuramoto_CondI_arc_invariance
-- name    : NonuniformKuramoto.CondI.arc_invariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:36.281891+00:00
-- url     : https://prove2.me/theorems/22b9b2f1-9500-44f2-b8f3-94f9fb341f0b
-- title:
--   Proof of Theorem V.3, p. 22 — under (26), $\bar\Delta(\gamma)$ is positively invariant for every $\gamma\in[\gamma_{\min},\gamma_{\max}]$
-- statement:
--   Consider the non-uniform Kuramoto model (8) with $n\ge2$, $D_i>0$, a symmetric complete coupling ($P_{ij}=P_{ji}>0$ for $i\ne j$), $\varphi_{ij}\in[0,\pi/2[$ for $i\ne j$ and $P_{ii}=\varphi_{ii}=0$. Assume condition (26), $\Gamma_{\min}>\Gamma_{\mathrm{critical}}$, and let $\gamma_{\min},\gamma_{\max}$ be as in Theorem V.3. Then for every
--
--   $$\gamma\in[\gamma_{\min},\gamma_{\max}]$$
--
--   the set $\bar\Delta(\gamma)$ is positively invariant: every solution of (8) whose phases at time $0$ lie in an arc of length $\gamma$ keeps all its phases in an arc of length $\gamma$ for all $t\ge0$.
--
--   This is the first half of statement 1) of Theorem V.3 (phase cohesiveness).
--
--   **Formalization Note** $\bar\Delta(\gamma)$ is stated on real lifts: all pairwise differences of the lift are at most $\gamma$, at time $0$ and, for the same continuous lift, at every $t\ge0$.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 22, proof of Theorem V.3 (V(θ(t)) non-increasing in ∆̄(γ), γ ∈ [γ_min, γ_max]); p. 20, Theorem V.3 1)

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model
import Definitions.Def_NonuniformKuramoto_CondI_Constants

namespace NonuniformKuramoto.CondI

/-- Proof of Theorem V.3, p. 22 (statement 1), first half): under (26), with `P = Pᵀ` complete, the
set `∆̄(γ)` is positively invariant for every `γ ∈ [γ_min, γ_max]`. -/
theorem arc_invariance {n : ℕ} (hn : 2 ≤ n) (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hD : ∀ i, 0 < D i) (hPsymm : ∀ i j, P i j = P j i)
    (hP : ∀ i j, i ≠ j → 0 < P i j) (hPii : ∀ i, P i i = 0) (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi / 2)
    (h26 : GammaCrit D ω P ϕ < GammaMin D P ϕ) :
    ∀ γ ∈ Set.Icc (gammaMin D ω P ϕ) (gammaMax D ω P ϕ),
      IsPosInvariant D ω P ϕ (ArcClosed γ) := by sorry

end NonuniformKuramoto.CondI
