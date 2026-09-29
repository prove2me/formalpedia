-- Prove2me | Theorems.Thm_MarkovMixing_heat_kernel_convergence
-- name    : MarkovMixing.heat_kernel_convergence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:39:30.772641+00:00
-- url     : https://prove2.me/theorems/9e30cc9e-5374-44ed-b355-b838875d5a32
-- title:
--   Continuous-time convergence without aperiodicity
-- statement:
--   Let $P$ be an **irreducible** Markov chain on a finite state space $V$ — aperiodicity is *not* assumed — with stationary distribution $\pi$. The **heat kernel** at real time $t$ is
--   $$H_t(x,y)=\sum_{k=0}^{\infty}e^{-t}\frac{t^k}{k!}\,P^k(x,y),$$
--   the law at time $t$ of the walk taking $P$-steps at the arrival times of a rate-one Poisson clock. Write $\|\mu-\nu\|_{TV}=\max_{A\subseteq V}|\mu(A)-\nu(A)|$ for the total variation distance and $d^{\mathrm{cont}}(t)=\max_x\|H_t(x,\cdot)-\pi\|_{TV}$.
--
--   The theorem (Theorem 20.1 of Levin–Peres–Wilmer) asserts:
--   $$d^{\mathrm{cont}}(t)\;\longrightarrow\;0\qquad(t\to\infty).$$
--
--   Every irreducible finite chain converges in continuous time — the periodicity obstruction that forces the aperiodicity hypothesis in the discrete Convergence Theorem (Mission II) simply disappears, because the Poisson number of completed jumps spreads over all residue classes: $H_t(x,x)>0$ for every $t>0$, so the continuous chain is automatically "aperiodic". This is the basic payoff of the continuous-time formalism and the reason laziness can always be traded for Poissonization.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 20.2, Theorem 20.1, p. 266

import Definitions.Def_mm_continuous

namespace MarkovMixing

/-- **Theorem 20.1** (LPW): for an irreducible chain — aperiodicity is *not*
needed — the heat kernel converges to the stationary distribution:
`max_x ‖H_t(x,·) − π‖_TV → 0` as `t → ∞`. -/
theorem heat_kernel_convergence {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : Irreducible P) (π : V → ℝ) (hπ : IsStationary P π) :
    Filter.Tendsto (fun t : ℝ => contDistStationary P π t)
      Filter.atTop (nhds 0) := by
  sorry

end MarkovMixing
