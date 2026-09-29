-- Prove2me | Theorems.Thm_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates
-- name    : IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/aae346a8-48a3-50ae-885b-b45cb9eb904a
-- title:
--   Noetherian local domains are dominated by discrete valuation rings
-- statement:
--   Let $R$ be a commutative ring which is an integral domain, Noetherian and local, and assume $R$ is not a field; let $K$ be a field equipped with an $R$-algebra structure making it a fraction field of $R$ (i.e. the structure map $R \to K$ exhibits $K$ as the localisation of $R$ at its nonzero elements). The assertion is that there exists a valuation subring $V$ of $K$ — a subring of $K$ such that for each $x \in K^{\times}$ at least one of $x$, $x^{-1}$ lies in $V$ — with the following three properties: $V$, viewed as a ring in its own right, is a discrete valuation ring; the image $\mathrm{algebraMap}\,R\,K\,(r)$ of every $r \in R$ lies in $V$, so that $R$ maps into $V$; and for every $r \in R$ one has $r \in \mathfrak m_R$, the maximal ideal of $R$, if and only if the image of $r$ in $K$ is a nonunit of $V$. The last two conditions say precisely that $V$ dominates $R$: the contraction along $R \to V$ of the maximal ideal of $V$ (its set of nonunits) is exactly $\mathfrak m_R$. The ring $R$ and the field $K$ may lie in different universes.
--
--   This is the classical existence statement for discrete valuation rings dominating a Noetherian local domain (EGA II 7.1.7), the reason why discrete valuation rings suffice in valuative criteria over a Noetherian base. It is used here for an integrality criterion tested on discrete valuation subrings, for a finiteness statement about geometrically connected pullbacks, and is refined by a variant producing a dominating discrete valuation ring with finite residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IsLocalRing

theorem IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (hR : ¬ IsField R)
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] :
    ∃ V : ValuationSubring K, IsDiscreteValuationRing ↥V ∧
      (∀ r : R, algebraMap R K r ∈ V) ∧
      (∀ r : R, r ∈ maximalIdeal R ↔ algebraMap R K r ∈ V.nonunits) := by sorry
