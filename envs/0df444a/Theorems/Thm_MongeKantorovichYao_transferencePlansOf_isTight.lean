-- Prove2me | Theorems.Thm_MongeKantorovichYao_transferencePlansOf_isTight
-- name    : MongeKantorovichYao.transferencePlansOf_isTight
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T19:46:05.295159+00:00
-- url     : https://prove2.me/theorems/ee5d4ac5-969a-47be-98b2-83e6c00ba9de
-- title:
--   Lemma 4.16 — tightness of transference plans
-- statement:
--   Let $X,Y$ be Polish spaces with their Borel σ-algebras, and let $M\subseteq\mathcal P(X)$ and $N\subseteq\mathcal P(Y)$ be tight sets of probability measures: for every $\varepsilon>0$ there is a compact $K\subseteq X$ with $\mu(X\setminus K)<\varepsilon$ for all $\mu\in M$, and similarly for $N$. Let $\Pi(M,N)$ be the set of probability measures on $X\times Y$ whose marginals on $X$ and $Y$ lie in $M$ and $N$ respectively. Then $\Pi(M,N)$ is tight in $\mathcal P(X\times Y)$.
--
--   Combined with Prokhorov's theorem, this yields convergent subsequences of transference plans, which is how the discrete case is passed to the limit.
--
--   **Formalization Note** Tightness is Mathlib's `IsTightMeasureSet`, which is equivalent to the $\varepsilon$–compact-set formulation of Definition 4.9.
-- source:
--   Colin Yao, *Monge–Kantorovich and Transportation Theory* (paper dated September 10, 2023), p. 10, Lemma 4.16 (tightness of transference), with Definition 4.9

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs

open MeasureTheory

namespace MongeKantorovichYao

theorem transferencePlansOf_isTight {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (M : Set (Measure X)) (N : Set (Measure Y))
    (hMprob : ∀ μ ∈ M, IsProbabilityMeasure μ) (hNprob : ∀ ν ∈ N, IsProbabilityMeasure ν)
    (hM : IsTightMeasureSet M) (hN : IsTightMeasureSet N) :
    IsTightMeasureSet (transferencePlansOf M N) := by sorry

end MongeKantorovichYao
