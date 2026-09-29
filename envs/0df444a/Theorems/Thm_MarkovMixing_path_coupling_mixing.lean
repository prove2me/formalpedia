-- Prove2me | Theorems.Thm_MarkovMixing_path_coupling_mixing
-- name    : MarkovMixing.path_coupling_mixing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:25:16.318418+00:00
-- url     : https://prove2.me/theorems/51338edf-87a5-4cca-8559-a9f67ca1bfe7
-- title:
--   Mixing bounds from path coupling
-- statement:
--   Let $P$ be a Markov chain on a finite state space $V$ with stationary distribution $\pi$, and suppose the path coupling hypotheses of Theorem 14.6 hold: a connected graph $G$ on $V$ with symmetric edge lengths $\ell\ge1$, a rate $\alpha>0$, and for every edge $\{x,y\}$ of $G$ a coupling of $P(x,\cdot),P(y,\cdot)$ contracting the path metric $\rho$ (least total $\ell$-length of a connecting walk) in expectation by $e^{-\alpha}$. Write $\mathrm{diam}(V)=\max_{x,y}\rho(x,y)$ for the path-metric diameter, $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$ for the total variation distance, $d(t)=\max_x\|P^t(x,\cdot)-\pi\|_{TV}$, and $t_{\mathrm{mix}}(\varepsilon)=\min\{t:d(t)\le\varepsilon\}$.
--
--   The theorem (Corollary 14.7 of Levin–Peres–Wilmer) asserts:
--
--   1. the distance to stationarity decays geometrically: $d(t)\le e^{-\alpha t}\,\mathrm{diam}(V)$ for every $t$;
--   2. consequently, for every $0<\varepsilon<1$, $\;t_{\mathrm{mix}}(\varepsilon)\le\bigl\lceil(-\log\varepsilon+\log\mathrm{diam}(V))/\alpha\bigr\rceil$.
--
--   The proof is one line from path coupling: iterating the one-step contraction bounds $\rho_K(P^t(x,\cdot),\pi)$ by $e^{-\alpha t}\mathrm{diam}(V)$, and the transportation distance dominates total variation because the path metric is at least $1$ between distinct states.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 14.2, Corollary 14.7, p. 192

import Definitions.Def_mm_transport
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **Corollary 14.7** (LPW): under the path coupling hypotheses,
`d(t) ≤ e^{-αt} diam(Ω)` and
`t_mix(ε) ≤ ⌈(−log ε + log diam(Ω))/α⌉`. -/
theorem path_coupling_mixing {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsStationary P π)
    (G : SimpleGraph V) (hconn : G.Connected)
    (ℓ : V → V → ℝ) (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y)
    (hℓsymm : ∀ x y : V, ℓ x y = ℓ y x)
    (α : ℝ) (hα : 0 < α)
    (hedge : ∀ x y : V, G.Adj x y →
      ∃ q : V × V → ℝ, IsCoupling (rowDist P 1 x) (rowDist P 1 y) q ∧
        ∑ p : V × V, q p * pathMetric G ℓ p.1 p.2 ≤ Real.exp (-α) * ℓ x y) :
    (∀ t : ℕ, distStationary P π t ≤
      Real.exp (-α * t) * ⨆ p : V × V, pathMetric G ℓ p.1 p.2) ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      (mixingTime P π ε : ℝ) ≤
        ⌈(-Real.log ε + Real.log (⨆ p : V × V, pathMetric G ℓ p.1 p.2)) / α⌉₊ := by
  sorry

end MarkovMixing
