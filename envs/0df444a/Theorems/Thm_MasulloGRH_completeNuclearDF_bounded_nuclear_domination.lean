-- Prove2me | Theorems.Thm_MasulloGRH_completeNuclearDF_bounded_nuclear_domination
-- name    : MasulloGRH.completeNuclearDF_bounded_nuclear_domination
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:39:13.573466+00:00
-- url     : https://prove2.me/theorems/96dc8eea-c94f-4473-b32b-8752ab5cb804
-- title:
--   Bounded sets of a complete nuclear (DF)-space are nuclearly dominated
-- statement:
--   Let $G$ be a complete nuclear (DF)-space over $\mathbb C$: $G$ is complete and nuclear, it has a fundamental sequence $(B_n)$ of bounded sets (every bounded set lies in some $B_n$), and every countable intersection of closed absolutely convex $0$-neighbourhoods which absorbs every bounded set is again a $0$-neighbourhood.
--
--   Then every bounded set $B \subseteq G$ is *nuclearly dominated*: there exist a bounded sequence $(y_n)$ in $G$ and nonnegative summable weights $(c_n) \in \ell^1$ such that for every continuous linear functional $f \in G'$ and every $x \in B$,
--   $$|f(x)| \le \sum_{n} c_n\, |f(y_n)|.$$
--
--   Equivalently, $B$ lies in the closed absolutely convex hull of $\{c_n y_n\}$ (up to normalisation). This is the bounded-set form of Grothendieck's theorem that the strong dual of a complete nuclear (DF)-space is a nuclear Fréchet space; it is the (DF)-analogue of the Fréchet statement `MasulloGRH.nuclearFrechet_bounded_nuclear_domination`. Proof idea: $F = G'_\beta$ is Fréchet; for the $0$-neighbourhood $U = B^\circ$ of $F$ choose, by nuclearity, $V = (B')^\circ$ with $F_V \to F_U$ nuclear, so $U^\circ$ lies in the weak-$*$ closed absolutely convex hull of a summable multiple of a sequence in $V^\circ$; since $G$ is complete and nuclear, $V^\circ = \overline{\Gamma}(B')$ is a compact subset of $G$.
-- source:
--   A. Grothendieck, Produits tensoriels topologiques (1955), Ch. II; H. H. Schaefer, Topological Vector Spaces, IV.9.6; A. M. Masullo, The Music of the Primes, Appendix C §C.2.4

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem completeNuclearDF_bounded_nuclear_domination (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hC : IsCompleteTVS G) (hN : IsNuclear G)
    (hB : ∃ B : ℕ → Set G, (∀ n, Bornology.IsVonNBounded ℂ (B n)) ∧
      ∀ S : Set G, Bornology.IsVonNBounded ℂ S → ∃ n, S ⊆ B n)
    (hDF : ∀ U : ℕ → Set G, (∀ n, U n ∈ nhds (0 : G) ∧ IsClosed (U n) ∧ Balanced ℂ (U n) ∧ Convex ℝ (U n)) →
      (∀ S : Set G, Bornology.IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) →
      (⋂ n, U n) ∈ nhds (0 : G))
    (B : Set G) (hBb : Bornology.IsVonNBounded ℂ B) :
    ∃ (y : ℕ → G) (c : ℕ → ℝ), Bornology.IsVonNBounded ℂ (Set.range y) ∧ (∀ n, 0 ≤ c n) ∧
      Summable c ∧ ∀ (f : StrongDual ℂ G), ∀ x ∈ B, ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖ := by sorry

end MasulloGRH
