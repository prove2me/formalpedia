-- Prove2me | Theorems.Thm_NonuniformKuramoto_PhaseSync_weighted_mean_conserved
-- name    : NonuniformKuramoto.PhaseSync.weighted_mean_conserved
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:14.56598+00:00
-- url     : https://prove2.me/theorems/cf113aef-7e10-4ef3-b3c8-8af9e6a66bc4
-- title:
--   (44), p. 27 — d/dt Dθ = −L(w_ij(t))θ in the rotating frame, so Σ D_iθ_i(t) = Σ D_iθ_i(0) + ω̄tΣ D_i
-- statement:
--   Under the hypotheses of Theorem V.10 ($n \ge 2$, $D_i > 0$, $P_{ij} \ge 0$ for $i \ne j$, $P_{ii} = 0$, a globally reachable node, $\varphi_{ij} = 0$, $\omega_i/D_i = \bar\omega$) and symmetric coupling $P = P^T$, let $\theta(t)$ be any solution on $[0,\infty)$, let $\psi(t) = \theta(t) - \bar\omega t\,\mathbf 1$ be its rotating-frame version and $w_{ij}(t) = P_{ij}\,\mathrm{sinc}(\theta_i(t) - \theta_j(t))$. Then for all $t \ge 0$
--
--   $$\frac{d}{dt} D\psi(t) = -L\big(w_{ij}(t)\big)\,\psi(t),$$
--
--   where $D = \mathrm{diag}(D_i)$ and $L$ is the Laplacian; consequently
--
--   $$\sum_{i=1}^n D_i\theta_i(t) = \sum_{i=1}^n D_i\theta_i(0) + \bar\omega\, t \sum_{i=1}^n D_i .$$
--
--   The second identity says the $D$-weighted mean angle rotates at the constant frequency $\bar\omega$; it identifies the limit of statement 2) of Theorem V.10.
--
--   **Formalization Note** No arc hypothesis is needed: both identities hold for every solution. The derivative is taken within $[0,\infty)$.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 27, (44)

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model
import Definitions.Def_NonuniformKuramoto_PhaseSync_Rate

namespace NonuniformKuramoto.PhaseSync

/-- (44), p. 27: under the hypotheses of Theorem V.10 and `P = Pᵀ`, in the rotating frame
`ψ(t) = θ(t) − ω̄ t 𝟏` every solution satisfies `d/dt Dψ = −L(wᵢⱼ(t)) ψ` with the symmetric
weights `wᵢⱼ(t) = Pᵢⱼ sinc(θᵢ(t) − θⱼ(t))`; consequently the weighted sum is conserved in the
rotating frame: `∑ᵢ Dᵢθᵢ(t) = ∑ᵢ Dᵢθᵢ(0) + ω̄ t ∑ᵢ Dᵢ`. -/
theorem weighted_mean_conserved {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) (ωbar : ℝ)
    (hn : 2 ≤ n) (hD : ∀ i, 0 < D i) (hP : ∀ i j, i ≠ j → 0 ≤ P i j)
    (hPii : ∀ i, P i i = 0) (hϕ : ∀ i j, ϕ i j = 0) (hω : ∀ i, ω i / D i = ωbar)
    (hreach : NonuniformKuramoto.CondI.HasGloballyReachableNode P) (hsymm : ∀ i j, P i j = P j i)
    (θ : ℝ → Fin n → ℝ) (hsol : NonuniformKuramoto.CondI.IsSolution D ω P ϕ θ) :
    (∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt (fun s : ℝ => fun i => D i * (θ s i - ωbar * s))
        (-((NonuniformKuramoto.CondI.lap (fun i j => P i j * Real.sinc (θ t i - θ t j))).mulVec
          (fun i => θ t i - ωbar * t)))
        (Set.Ici 0) t) ∧
    (∀ t : ℝ, 0 ≤ t →
      ∑ i, D i * θ t i = ∑ i, D i * θ 0 i + ωbar * t * ∑ i, D i) := by sorry

end NonuniformKuramoto.PhaseSync
