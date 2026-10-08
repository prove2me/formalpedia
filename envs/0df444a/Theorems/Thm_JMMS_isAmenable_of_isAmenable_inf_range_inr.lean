-- Prove2me | Theorems.Thm_JMMS_isAmenable_of_isAmenable_inf_range_inr
-- name    : JMMS.isAmenable_of_isAmenable_inf_range_inr
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T09:23:37.441293+00:00
-- url     : https://prove2.me/theorems/91150653-c02b-4a1e-86c5-4fa9b5f45704
-- title:
--   Corollary 1.4 — a subgroup H of F(X) ⋊ G is amenable when H ∩ ({1} × G) is
-- statement:
--   Let $F$ be a functor from finite sets and injective maps to groups with amenable values, let a group $G$ act extensively amenably on a set $X$, and let $H$ be a subgroup of the semidirect product $F(X) \rtimes G$. If the intersection of $H$ with the copy $\{1\} \times G$ of $G$ is amenable, then $H$ is amenable.
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 3: “Corollary 1.4. Let $G \curvearrowright X$ be an extensively amenable action and let $F\colon \mathbf I \to \mathbf{Amen}$ be any functor. A subgroup $H$ of $F(X) \rtimes G$ is amenable as soon as the intersection $H \cap (\{1\} \times G)$ is so.”
--
--   The published statement [`ThompsonAmenability.isAmenable_of_isExtensivelyAmenableOn_of_cocycle`](https://prove2.me/theorems/dd4dc306-5e82-47e1-8ed8-724ca46e62c8) is the case of the lamp functor with an abelian lamp group and a free affine action.
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 3, Corollary 1.4

import Mathlib
import Definitions.Def_IntervalExchange

open IntervalExchange

namespace JMMS

universe u v

theorem isAmenable_of_isAmenable_inf_range_inr
    (F : CategoryTheory.Functor FinInj.{u} GrpCat.{u}) (hF : IsAmenableValued F)
    (G : Type v) [Group G] (X : Type u) [MulAction G X] (hGX : IsExtensivelyAmenable G X)
    (H : Subgroup (FunctorProduct F G X))
    (hH : Garrido.IsAmenable ↥(H ⊓ (SemidirectProduct.inr : G →* FunctorProduct F G X).range)) :
    Garrido.IsAmenable ↥H := by
  sorry

end JMMS
