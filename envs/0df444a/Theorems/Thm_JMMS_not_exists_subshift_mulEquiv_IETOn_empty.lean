-- Prove2me | Theorems.Thm_JMMS_not_exists_subshift_mulEquiv_IETOn_empty
-- name    : JMMS.not_exists_subshift_mulEquiv_IETOn_empty
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T14:44:38.247011+00:00
-- url     : https://prove2.me/theorems/f5ab6744-b5d5-4538-aab4-b3a97410802f
-- title:
--   JMMS Proposition 5.11 needs Σ nonempty — IET(Λ; ∅) is not the topological full group of a minimal Cantor Λ-subshift
-- statement:
--   Let $\Lambda \le \mathbf R/\mathbf Z$ be infinite and finitely generated. There is no Cantor minimal $\Lambda$-subshift $X$ over a finite alphabet whose topological full group $[[\Lambda]]$ is isomorphic to $\mathrm{IET}(\Lambda; \emptyset)$.
--
--   This is a printed-fails lemma for JMMS Proposition 5.11, p. 21, with $\Sigma = \emptyset$: “There is a minimal $\Lambda$-subshift $(\Lambda, X)$, an isomorphism $\pi : [[\Lambda]] \to \mathrm{IET}(\Lambda; \Sigma)$ and a continuous surjective map $h : X \to \mathbf R/\mathbf Z$ such that $h(g \cdot x) = \pi(g) \cdot x$ for all $x \in X$ and $g \in [[\Lambda]]$.” It is not a claim of the paper. It shows that the published statement `JMMS.exists_isMinimal_subshift_mulEquiv_IETOn` needs its hypothesis that $\Sigma$ is nonempty: $\mathrm{IET}(\Lambda; \emptyset)$ consists of the rotations by $\Lambda$, which commute, while the topological full group of a minimal Cantor system does not commute.
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 21, Proposition 5.11 with Σ empty (printed-fails lemma, not in the paper)

import Mathlib
import Definitions.Def_CantorSystems

open CantorSystems IntervalExchange

namespace JMMS

theorem not_exists_subshift_mulEquiv_IETOn_empty
    (Λ : AddSubgroup UnitAddCircle) (hΛ : (Λ : Set UnitAddCircle).Infinite) (hfg : Λ.FG) :
    ¬ ∃ k : ℕ, ∃ S : Subshift Λ (Fin k), IsCantorSpace S ∧ AddAction.IsMinimal Λ S ∧
      Nonempty (topologicalFullGroup Λ S ≃* IETOn Λ ∅) := by
  sorry

end JMMS
