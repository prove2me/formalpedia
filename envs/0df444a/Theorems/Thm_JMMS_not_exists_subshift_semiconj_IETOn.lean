-- Prove2me | Theorems.Thm_JMMS_not_exists_subshift_semiconj_IETOn
-- name    : JMMS.not_exists_subshift_semiconj_IETOn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T14:45:27.392989+00:00
-- url     : https://prove2.me/theorems/dd2aa55a-728d-47fc-9fb4-7cdb14645a8b
-- title:
--   The semiconjugacy printed in JMMS Proposition 5.11 cannot hold at every point
-- statement:
--   Let $\Lambda \le \mathbf R/\mathbf Z$ be infinite and finitely generated, and let $\Sigma \subset \mathbf R/\mathbf Z$ be finite and nonempty. There are no $\Lambda$-subshift $X$ over a finite alphabet, group isomorphism $\pi : [[\Lambda]] \to \mathrm{IET}(\Lambda; \Sigma)$ and continuous surjection $h : X \to \mathbf R/\mathbf Z$ with $h(g \cdot x) = \pi(g)(h(x))$ for all $x \in X$ and all $g \in [[\Lambda]]$.
--
--   This is a printed-fails lemma for JMMS Proposition 5.11, p. 21: “There is a minimal $\Lambda$-subshift $(\Lambda, X)$, an isomorphism $\pi : [[\Lambda]] \to \mathrm{IET}(\Lambda; \Sigma)$ and a continuous surjective map $h : X \to \mathbf R/\mathbf Z$ such that $h(g \cdot x) = \pi(g) \cdot x$ for all $x \in X$ and $g \in [[\Lambda]]$.” It is not a claim of the paper. It shows that the equation, read as $h(g \cdot x) = \pi(g)(h(x))$, must be restricted, as in the published statement `JMMS.exists_isMinimal_subshift_mulEquiv_IETOn`, to the points $x$ with $h(x) \notin \Sigma + \Lambda$.
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 21, Proposition 5.11 (printed-fails lemma, not in the paper)

import Mathlib
import Definitions.Def_CantorSystems

open CantorSystems IntervalExchange

namespace JMMS

theorem not_exists_subshift_semiconj_IETOn
    (Λ : AddSubgroup UnitAddCircle) (hΛ : (Λ : Set UnitAddCircle).Infinite) (hfg : Λ.FG)
    (σ : Finset UnitAddCircle) (hσ : σ.Nonempty) :
    ¬ ∃ k : ℕ, ∃ S : Subshift Λ (Fin k),
      ∃ π : topologicalFullGroup Λ S ≃* IETOn Λ σ, ∃ h : S → UnitAddCircle,
        Continuous h ∧ Function.Surjective h ∧
        ∀ (g : topologicalFullGroup Λ S) (x : S),
          h ((g : S ≃ₜ S) x) = (π g : Equiv.Perm UnitAddCircle) (h x) := by
  sorry

end JMMS
