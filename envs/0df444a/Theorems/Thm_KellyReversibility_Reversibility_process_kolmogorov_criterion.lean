-- Prove2me | Theorems.Thm_KellyReversibility_Reversibility_process_kolmogorov_criterion
-- name    : KellyReversibility.Reversibility.process_kolmogorov_criterion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:36:04.582994+00:00
-- url     : https://prove2.me/theorems/4de6143f-f77d-4ce8-8564-85f0e5169ca4
-- title:
--   Theorem 1.8 — Kolmogorov's criterion: a stationary Markov process is reversible iff (1.22) holds
-- statement:
--   Let $X(t)$, $t\in\mathbb R$, be a stationary Markov process on a finite state space $\mathcal S$ with transition rates $q(j,k)\ge 0$ ($q(j,j)=0$), irreducible, with equilibrium distribution $\pi$. The process is reversible if and only if its transition rates satisfy
--   $$q(j_1,j_2)q(j_2,j_3)\cdots q(j_{n-1},j_n)q(j_n,j_1)=q(j_1,j_n)q(j_n,j_{n-1})\cdots q(j_3,j_2)q(j_2,j_1) \tag{1.22}$$
--   for any finite sequence of states $j_1,j_2,\dots,j_n\in\mathcal S$.
--
--   Reversibility, a property of the joint laws of the process at all finite sets of times, is thus decided by the rates alone: a reversible process shows no net circulation around any cycle of states.
--
--   **Formalization Note** Reversibility is the distributional definition of p. 5: the finite-dimensional distributions $\pi(j_1)\prod_r e^{(t_{r+1}-t_r)Q}(j_r,j_{r+1})$ are invariant under $t\mapsto\tau-t$. It is not defined as detailed balance, and two-way communication ($q(j,k)>0\iff q(k,j)>0$) is not assumed. The sequences in (1.22) have arbitrary length and may repeat states. The state space is finite (Kelly allows a countable one).
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 23, Theorem 1.8, Eq. (1.22)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Reversibility_StationaryLaw
import Definitions.Def_KellyReversibility_Reversibility_MarkovProcess

namespace KellyReversibility.Reversibility

/-- Theorem 1.8 (Kelly, p. 23). -/
theorem process_kolmogorov_criterion {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → S → ℝ) (hq : ∀ j k, j ≠ k → 0 ≤ q j k) (hq0 : ∀ j, q j j = 0)
    (hirr : RatesIrreducible q)
    (π₀ : S → ℝ) (hπ₀ : IsEquilibrium π₀ q) :
    ProcessReversible q π₀ ↔ KolmogorovCycle q := by sorry

end KellyReversibility.Reversibility
