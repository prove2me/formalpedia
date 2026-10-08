-- Prove2me | Theorems.Thm_JMMS_exists_lipschitz_embedding_and_isAmenable_IET_of_isExtensivelyAmenable_of_hasPolynomialGrowth
-- name    : JMMS.exists_lipschitz_embedding_and_isAmenable_IET_of_isExtensivelyAmenable_of_hasPolynomialGrowth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T09:32:00.032074+00:00
-- url     : https://prove2.me/theorems/9b2a68c8-7677-47a3-8f31-643b90571054
-- title:
--   p. 6 — Schreier graphs of subgroups of IET embed in ℤ^d, so a positive answer to Question 1.11 implies that IET is amenable
-- statement:
--   Two statements:
--
--   1. For every finitely generated subgroup $G$ of $\mathrm{IET}$, with a finite symmetric generating set $S$, and every $x \in \mathbf R/\mathbf Z$, the Schreier graph of $G$ on the orbit $Gx$ admits an injective Lipschitz map into some $\mathbf Z^d$: a map $f$, injective on $Gx$, with $d(f(sy), f(y)) \le C$ for every $y \in Gx$ and $s \in S$.
--   2. Suppose that every transitive action of a group $G$ on a set $X$ whose Schreier graph, for some finite symmetric generating set $S$ and some point $x_0$, grows polynomially is extensively amenable (the positive answer to Question 1.11, for groups and sets in the lowest universe). Then $\mathrm{IET}$ is amenable.
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 6: “A positive answer to Question 1.11 would imply that the whole group IET is amenable, as the Schreier graph of any finitely generated subgroup $G < \mathrm{IET}$ admit an injective Lipschitz embedding into $\mathbf Z^d$ (see § 5).”
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 6, the remark after Question 1.11

import Mathlib
import Definitions.Def_IntervalExchange

open IntervalExchange

namespace JMMS

theorem exists_lipschitz_embedding_and_isAmenable_IET_of_isExtensivelyAmenable_of_hasPolynomialGrowth :
    (∀ (G : Subgroup (Equiv.Perm UnitAddCircle)), G ≤ IET →
      ∀ S : Finset (Equiv.Perm UnitAddCircle), (∀ s ∈ S, s ∈ G ∧ s⁻¹ ∈ S) →
        Subgroup.closure (S : Set (Equiv.Perm UnitAddCircle)) = G →
        ∀ x : UnitAddCircle, ∃ (d : ℕ) (f : UnitAddCircle → (Fin d → ℤ)) (C : ℝ),
          Set.InjOn f (MulAction.orbit G x) ∧
            ∀ y ∈ MulAction.orbit G x, ∀ s ∈ S, dist (f (s y)) (f y) ≤ C) ∧
    ((∀ (G X : Type) [Group G] [MulAction G X] [MulAction.IsPretransitive G X] (S : Finset G),
      (∀ s ∈ S, s⁻¹ ∈ S) → Subgroup.closure (S : Set G) = ⊤ → ∀ x₀ : X,
        HasPolynomialGrowth (S : Set G) x₀ → IsExtensivelyAmenable G X) →
      Garrido.IsAmenable ↥IET) := by
  sorry

end JMMS
