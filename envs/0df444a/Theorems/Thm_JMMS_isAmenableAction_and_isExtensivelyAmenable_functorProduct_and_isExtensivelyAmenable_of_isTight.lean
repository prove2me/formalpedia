-- Prove2me | Theorems.Thm_JMMS_isAmenableAction_and_isExtensivelyAmenable_functorProduct_and_isExtensivelyAmenable_of_isTight
-- name    : JMMS.isAmenableAction_and_isExtensivelyAmenable_functorProduct_and_isExtensivelyAmenable_of_isTight
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T09:22:57.174133+00:00
-- url     : https://prove2.me/theorems/2ddd3e27-fc21-491a-b965-aec7be4b3884
-- title:
--   Theorem 1.3 — G ↷ X is extensively amenable exactly when F(X) ⋊ G ↷ F(X) is amenable, for tight F
-- statement:
--   Let $F$ be a functor from the category $I$ of finite sets and injective maps to groups, with amenable values, and let $F(X)$ be its extension to a set $X$ by the direct limit over the finite subsets of $X$. Let a group $G$ act on $X$, so that $G$ acts on $F(X)$ by automorphisms and the semidirect product $F(X) \rtimes G$ acts on $F(X)$ by $(a, g) \cdot b = a \cdot g(b)$. Then:
--
--   1. if the action of $G$ on $X$ is extensively amenable, the action of $F(X) \rtimes G$ on $F(X)$ is amenable and extensively amenable;
--   2. if the action of $F(X) \rtimes G$ on $F(X)$ is amenable and $F$ is tight on $X$ (for no $x \in X$ is the map $F(X \setminus \{x\}) \to F(X)$ induced by inclusion onto), the action of $G$ on $X$ is extensively amenable.
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 3: “Theorem 1.3. Let $F\colon \mathbf I \to \mathbf{Amen}$ be any functor, extended to arbitrary sets as described above. Let $G$ be a group acting on a set $X$. If the action $G \curvearrowright X$ is extensively amenable, then the action $F(X) \rtimes G \curvearrowright F(X)$ is amenable. Moreover it is extensively amenable. Conversely, assume that the action $F(X) \rtimes G \curvearrowright F(X)$ is amenable. Then $G \curvearrowright X$ is extensively amenable provided $F$ is tight on $X$.”
--
--   The finite sets of $I$, and the values of $F$, are taken in one universe, the universe of $X$.
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 3, Theorem 1.3

import Mathlib
import Definitions.Def_IntervalExchange

open IntervalExchange

namespace JMMS

universe u v

theorem isAmenableAction_and_isExtensivelyAmenable_functorProduct_and_isExtensivelyAmenable_of_isTight
    (F : CategoryTheory.Functor FinInj.{u} GrpCat.{u}) (hF : IsAmenableValued F)
    (G : Type v) [Group G] (X : Type u) [MulAction G X] :
    (IsExtensivelyAmenable G X →
      IsAmenableAction (FunctorProduct F G X) (extend F X) ∧
        IsExtensivelyAmenable (FunctorProduct F G X) (extend F X)) ∧
    (IsAmenableAction (FunctorProduct F G X) (extend F X) → IsTight F X →
      IsExtensivelyAmenable G X) := by
  sorry

end JMMS
