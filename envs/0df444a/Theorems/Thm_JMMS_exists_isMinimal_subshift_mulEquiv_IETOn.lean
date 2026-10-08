-- Prove2me | Theorems.Thm_JMMS_exists_isMinimal_subshift_mulEquiv_IETOn
-- name    : JMMS.exists_isMinimal_subshift_mulEquiv_IETOn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T14:44:37.853569+00:00
-- url     : https://prove2.me/theorems/c5289eef-7de2-4bd4-9d07-d48c50370a5d
-- title:
--   JMMS, Proposition 5.11 — IET(Λ; Σ) is the topological full group of a minimal Λ-subshift
-- statement:
--   Let $\Lambda \le \mathbf R/\mathbf Z$ be infinite and finitely generated, and let $\Sigma \subset \mathbf R/\mathbf Z$ be finite and nonempty. Then there are a Cantor minimal $\Lambda$-subshift $X$ over a finite alphabet, a group isomorphism $\pi : [[\Lambda]] \to \mathrm{IET}(\Lambda; \Sigma)$ from the topological full group of $X$, and a continuous surjection $h : X \to \mathbf R/\mathbf Z$ such that $h(g \cdot x) = \pi(g)(h(x))$ for every $g \in [[\Lambda]]$ and every $x$ with $h(x) \notin \Sigma + \Lambda$.
--
--   JMMS, p. 21: “Proposition 5.11. Let $\Lambda < \mathbf R/\mathbf Z$ be infinite and finitely generated and $\Sigma$ as above. There is a minimal $\Lambda$-subshift $(\Lambda, X)$, an isomorphism $\pi : [[\Lambda]] \to \mathrm{IET}(\Lambda; \Sigma)$ and a continuous surjective map $h : X \to \mathbf R/\mathbf Z$ such that $h(g \cdot x) = \pi(g) \cdot x$ for all $x \in X$ and $g \in [[\Lambda]]$.”
--
--   *Formalization note.* As printed, the right-hand side $\pi(g) \cdot x$ applies a map of $\mathbf R/\mathbf Z$ to a point of $X$; the intended equation is $h(g \cdot x) = \pi(g)(h(x))$. Even so corrected, it cannot hold at every $x$: a $g$ with a discontinuity at $y$ and continuity of $h$ and of $\pi^{-1}(g)$ give a contradiction at a point over $y$ (the printed-fails lemma `JMMS.not_exists_subshift_semiconj_IETOn`). JMMS's construction doubles each point of $\Sigma + \Lambda$ into a left and a right copy, so the equation is required only off those points: for $h(x) \notin \Sigma + \Lambda$. $\Sigma$ is nonempty, as $\Sigma = \{x_1, \dots, x_r\}$ is in the paper; for $\Sigma = \emptyset$ the claim fails (`JMMS.not_exists_subshift_mulEquiv_IETOn_empty`). JMMS's subshifts are Cantor systems (p. 20), so $X$ is a Cantor space. Minimality is Mathlib's (every orbit is dense), equivalent for the continuous shift action to JMMS's “no non-trivial closed $\Gamma$-invariant subsets” (`isMinimal_iff_isClosed_vadd_invariant`).
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 21, Proposition 5.11

import Mathlib
import Definitions.Def_CantorSystems

open CantorSystems IntervalExchange

namespace JMMS

theorem exists_isMinimal_subshift_mulEquiv_IETOn
    (Λ : AddSubgroup UnitAddCircle) (hΛ : (Λ : Set UnitAddCircle).Infinite) (hfg : Λ.FG)
    (σ : Finset UnitAddCircle) (hσ : σ.Nonempty) :
    ∃ k : ℕ, ∃ S : Subshift Λ (Fin k), IsCantorSpace S ∧ AddAction.IsMinimal Λ S ∧
      ∃ π : topologicalFullGroup Λ S ≃* IETOn Λ σ, ∃ h : S → UnitAddCircle,
        Continuous h ∧ Function.Surjective h ∧
        ∀ (g : topologicalFullGroup Λ S) (x : S), h x ∉ cosetsOf Λ σ →
          h ((g : S ≃ₜ S) x) = (π g : Equiv.Perm UnitAddCircle) (h x) := by
  sorry

end JMMS
