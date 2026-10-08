-- Prove2me | Theorems.Thm_KellyReversibility_Reversibility_entropy_strictly_increasing
-- name    : KellyReversibility.Reversibility.entropy_strictly_increasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:35:42.287439+00:00
-- url     : https://prove2.me/theorems/c4528cb4-8ae0-454b-8f5a-73c02af22bf5
-- title:
--   Theorem 1.6 — $H(t)=\sum_j\pi(j)h(u_j(t)/\pi(j))$ is strictly increasing out of equilibrium
-- statement:
--   Let $X(t)$ be a Markov process on a finite state space $\mathcal S$ with transition rates $q(j,k)$ ($q(j,j)=0$), irreducible, with equilibrium distribution $\pi$. Let the initial distribution $u(0)=(u_j(0))_{j\in\mathcal S}$ be any probability distribution and $u_j(t)=P(X(t)=j)$ the solution of the forward equations
--   $$\frac{d}{dt}u_j(t)=\sum_{k}\bigl(u_k(t)q(k,j)-u_j(t)q(j,k)\bigr),\qquad j\in\mathcal S, \tag{1.16}$$
--   and let $h$ be a strictly concave function on $[0,\infty)$ and
--   $$H(t)=\sum_{j\in\mathcal S}\pi(j)\,h\!\left(\frac{u_j(t)}{\pi(j)}\right).$$
--   If the initial distribution is not the equilibrium distribution, then $H(t)$, $t>0$, is strictly increasing.
--
--   With $h(x)=-x\log x$, $H$ is the entropy of $u(t)$ relative to $\pi$; the theorem holds whether or not the process is reversible.
--
--   **Formalization Note** $u(t)=u(0)e^{tQ}$ is the solution of (1.16). "Strictly increasing for $t>0$" is `StrictMonoOn H (Set.Ioi 0)`. Strict concavity is required on $[0,\infty)$, where the ratios $u_j(t)/\pi(j)$ lie. The state space is finite, as on p. 17.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 17–18, Theorem 1.6 (setting and Eq. (1.16) on pp. 17–18)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Reversibility_StationaryLaw
import Definitions.Def_KellyReversibility_Reversibility_MarkovProcess

namespace KellyReversibility.Reversibility

/-- Theorem 1.6 (Kelly, p. 18). -/
theorem entropy_strictly_increasing {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → S → ℝ) (hq : ∀ j k, j ≠ k → 0 ≤ q j k) (hq0 : ∀ j, q j j = 0)
    (hirr : RatesIrreducible q)
    (π : S → ℝ) (hπ : IsEquilibrium π q)
    (h : ℝ → ℝ) (hh : StrictConcaveOn ℝ (Set.Ici 0) h)
    (u₀ : S → ℝ) (hu₀ : ∀ j, 0 ≤ u₀ j) (hu₀1 : ∑ j, u₀ j = 1) (hne : u₀ ≠ π) :
    StrictMonoOn (entropyH q π h u₀) (Set.Ioi 0) := by sorry

end KellyReversibility.Reversibility
