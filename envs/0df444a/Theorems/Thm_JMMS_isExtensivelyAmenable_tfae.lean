-- Prove2me | Theorems.Thm_JMMS_isExtensivelyAmenable_tfae
-- name    : JMMS.isExtensivelyAmenable_tfae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T09:22:16.059156+00:00
-- url     : https://prove2.me/theorems/6d161d92-a7b8-41b2-a444-e8209a21224e
-- title:
--   Lemma 2.2 — four equivalent forms of extensive amenability
-- statement:
--   For an action of a group $G$ on a set $X$, the following are equivalent:
--
--   1. the action is extensively amenable;
--   2. for every finitely generated subgroup $H$ of $G$ and every $x \in X$, the action of $H$ on the orbit $Hx$ is extensively amenable;
--   3. for every finitely generated subgroup $H$ and every $x_0 \in X$, there is an $H$-invariant mean on the finite subsets of the orbit $Hx_0$ that gives nonzero weight to the sets containing $x_0$;
--   4. there is a $G$-invariant mean on the finite subsets of $X$ that gives nonzero weight to the sets containing $x_0$, for every $x_0 \in X$.
--
--   Means are finitely additive measures of total mass $1$ on all sets of finite subsets, and invariance means invariance under the induced action on finite subsets.
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 7: “Lemma 2.2. Let $G$ be a group acting on a set $X$. The following are equivalent: (i) The action of $G$ on $X$ is extensively amenable. (ii) For every finitely generated subgroup $H$ of $G$ and every $H$-orbit $Y \subset X$, the action of $H$ on $Y$ is extensively amenable. (iii) For every finitely generated subgroup $H$ of $G$ and every $x_0 \in X$, there is an $H$-invariant mean on $\mathscr P_{\mathrm f}(Hx_0)$ that gives nonzero weight to $\{A \in \mathscr P_{\mathrm f}(Hx_0), x_0 \in A\}$. (iv) There is a $G$-invariant mean on $\mathscr P_{\mathrm f}(X)$ that gives nonzero weight to $\{A \in \mathscr P_{\mathrm f}(X), x_0 \in A\}$ for all $x_0 \in X$.”
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 7, Lemma 2.2

import Mathlib
import Definitions.Def_IntervalExchange

open IntervalExchange
open scoped ENNReal

namespace JMMS

theorem isExtensivelyAmenable_tfae {G X : Type*} [Group G] [MulAction G X] :
    List.TFAE
      [IsExtensivelyAmenable G X,
       ∀ H : Subgroup G, H.FG → ∀ x : X, IsExtensivelyAmenable H (MulAction.orbit H x),
       ∀ H : Subgroup G, H.FG → ∀ x₀ : X,
         ∃ m : Set (Finset (MulAction.orbit H x₀)) → ℝ≥0∞, Garrido.IsFinitelyAdditiveMeasure m ∧
           m Set.univ = 1 ∧
           (∀ (h : H) (S : Set (Finset (MulAction.orbit H x₀))),
             m ((fun E => E.map
               (MulAction.toPerm h : Equiv.Perm (MulAction.orbit H x₀)).toEmbedding) '' S) = m S) ∧
           m {E | ⟨x₀, MulAction.mem_orbit_self x₀⟩ ∈ E} ≠ 0,
       ∃ m : Set (Finset X) → ℝ≥0∞, Garrido.IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧
         (∀ (g : G) (S : Set (Finset X)),
           m ((fun E => E.map (MulAction.toPerm g : Equiv.Perm X).toEmbedding) '' S) = m S) ∧
         ∀ x₀ : X, m {E | x₀ ∈ E} ≠ 0] := by
  sorry

end JMMS
