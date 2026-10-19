-- Prove2me | Theorems.Thm_HeathcoteUnbounded_state_outside_position_momentum_domains
-- name    : HeathcoteUnbounded.state_outside_position_momentum_domains
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T14:36:59.980539+00:00
-- url     : https://prove2.me/theorems/f7087546-b989-4962-b25a-bbcf2bec7098
-- title:
--   A normalized state of $L^2(\mathbb R)$ outside both $D(Q)$ and $D(P)$
-- statement:
--   There is a unit vector $\varphi\in L^2(\mathbb R)$ — namely the class of Heathcote's function $\psi(x)=x^{-1}\mathbf 1_{[1,\infty)}(x)$ of eq. (4) — such that
--
--   $$\|\varphi\|_{L^2}=1,\qquad \varphi\notin D(Q),\qquad \varphi\notin D(P),$$
--
--   where $D(Q)$ and $D(P)$ are the domains of the position and momentum operators. So, under Postulate 1 (every normed ray is a state), there are states on which neither the position nor the momentum operator acts.
--
--   **Formalization Note** $\varphi$ is required to be a.e. equal to `psi`; the domains are the sets `positionDomain` and `momentumDomain` of $L^2$ elements.
-- source:
--   A. Heathcote, "Unbounded Operators and the Incompleteness of Quantum Mechanics", Philosophy of Science 57 (1990), 523–534, pp. 4–6, eqs. (3)–(4)

import Mathlib
import Definitions.Def_HeathcoteUnbounded_Psi
import Definitions.Def_HeathcoteUnbounded_PositionDomain
import Definitions.Def_HeathcoteUnbounded_MomentumDomain

open MeasureTheory

namespace HeathcoteUnbounded

theorem state_outside_position_momentum_domains :
    ∃ φ : Lp ℂ 2 (volume : Measure ℝ), (φ : ℝ → ℂ) =ᵐ[volume] psi ∧ ‖φ‖ = 1 ∧
      φ ∉ positionDomain ∧ φ ∉ momentumDomain := by sorry

end HeathcoteUnbounded
