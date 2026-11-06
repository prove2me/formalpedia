-- Prove2me | Theorems.Thm_KMPMixing_fact_2_5
-- name    : KMPMixing.fact_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:10:30.714463+00:00
-- url     : https://prove2.me/theorems/22578889-0241-4c24-a8ac-29d004c6cae4
-- title:
--   Fact 2.5 — $\delta(k)\le(2\varepsilon)^{\lfloor k/\ell\rfloor}$ once $\delta(\ell)\le\varepsilon<1/2$
-- statement:
--   Let $M$ be the transition matrix of a Markov chain on a finite state space $\Omega$ with stationary distribution $\pi$, and let $\delta(k)=\max_{x\in\Omega}\|M^k(x,\cdot)-\pi\|_{\mathrm{TV}}$. If $\delta(\ell)\le\varepsilon$ for some positive integer $\ell$ and $0<\varepsilon<1/2$, then for every integer $k\ge0$,
--   $$
--   \delta(k)\le(2\varepsilon)^{\lfloor k/\ell\rfloor}.
--   $$
--
--   One window of accuracy $\varepsilon<1/2$ yields geometric decay of the distance to stationarity.
--
--   Differences from the source: none.
-- source:
--   Chen et al., arXiv:2609.38044, Fact 2.5, p.12 (PDF p.14) ([LP17, Lemmas 4.10 and 4.11])

import Mathlib
import Definitions.Def_mm_mixing
open MarkovMixing

namespace KMPMixing

/-- **Fact 2.5** (arXiv:2609.38044, p.12 (PDF p.14); [LP17, Lemmas 4.10 and 4.11]). Let `M` be the
transition matrix of a Markov chain on a finite state space `Ω` with stationary distribution `π`.
If `δ(ℓ) ≤ ε` for some positive integer `ℓ` and `0 < ε < 1/2`, then for every integer `k ≥ 0`,
`δ(k) ≤ (2ε)^{⌊k/ℓ⌋}`.

**Formalization Note** `δ(k) = max_x ‖M^k(x, ·) − π‖_TV` is `MarkovMixing.distStationary`;
`⌊k/ℓ⌋` is natural-number division. The state space is any finite type; it is nonempty because
`π` is a distribution. -/
theorem fact_2_5 {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (hM : IsStochastic M) (π : V → ℝ) (hπ : IsStationary M π)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (hδ : distStationary M π ℓ ≤ ε) (k : ℕ) :
    distStationary M π k ≤ (2 * ε) ^ (k / ℓ) := by sorry

end KMPMixing
