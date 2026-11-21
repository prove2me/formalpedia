-- Prove2me | Theorems.Thm_NuclearSpaces_completeDF_bounded_series_expansion
-- name    : NuclearSpaces.completeDF_bounded_series_expansion
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-20T23:59:16.441318+00:00
-- url     : https://prove2.me/theorems/38b89e93-fbb8-4084-b801-0ed5f78465a6
-- title:
--   Bounded sets in complete nuclear (DF)-spaces admit uniformly summable series representations
-- statement:
--   Let $G$ be a complete nuclear Hausdorff locally convex space over $\mathbb C$ with the following two $(DF)$ properties: it has a countable fundamental family of bounded sets, and every countable intersection of closed, balanced, convex zero-neighbourhoods that absorbs every bounded set is itself a zero-neighbourhood.
--
--   For every bounded subset $B\subseteq G$, there exist a bounded sequence $(y_n)$ in $G$ and a nonnegative summable real sequence $(c_n)$ such that every point of $B$ admits a series representation with the same coefficient bounds:
--
--   $$\forall x\in B,\quad \exists (a_n)\in\mathbb C^{\mathbb N},\qquad |a_n|\le c_n\quad\text{and}\quad x=\sum_{n=0}^{\infty}a_n y_n.$$
--
--   The sum converges unconditionally in the given topology of $G$; formally this is `HasSum`, not a totalized sum without a convergence assertion. The sequence $(y_n)$ and the envelope $(c_n)$ are independent of $x$.
--
--   This result gives a common summable coefficient envelope for an entire bounded set. It is a scalar-factor specialization of Grothendieck's bounded-disk tensor-series theorem (section 2.4, Theorem 5), and provides the series-construction step needed for bounded nuclear domination in the mission's nuclear-duality argument.
--
--   Formalization note: this theorem is an open obligation. Its proof must construct the series independently of the target `MasulloGRH.completeNuclearDF_bounded_nuclear_domination` and of any strong-dual nuclearity theorem that reduces to that target.
-- source:
--   A. Grothendieck, Résumé des résultats essentiels dans la théorie des produits tensoriels topologiques et des espaces nucléaires, Annales de l'Institut Fourier 4 (1952), pp. 73–112, section 2.4, Theorem 5, original p. 104. English translation: https://translations.thosgood.net/AIF-4-1952-73.html#section-2.4 (PDF https://translations.thosgood.net/AIF-4-1952-73.pdf, p. 21). The submitted statement is the complete scalar-factor specialization, with an explicit uniform coefficient envelope. Application: Masullo, The Music of the Primes, frozen 20 November 2026 draft, Appendix C section C.2.4, especially Lemma C.2.4.11, p. 689.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false
open MasulloGRH

theorem NuclearSpaces.completeDF_bounded_series_expansion
    (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hC : IsCompleteTVS G) (hN : IsNuclear G)
    (hB : ∃ B : ℕ → Set G, (∀ n, Bornology.IsVonNBounded ℂ (B n)) ∧
      ∀ S : Set G, Bornology.IsVonNBounded ℂ S → ∃ n, S ⊆ B n)
    (hDF : ∀ U : ℕ → Set G, (∀ n, U n ∈ nhds (0 : G) ∧ IsClosed (U n) ∧ Balanced ℂ (U n) ∧ Convex ℝ (U n)) →
      (∀ S : Set G, Bornology.IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) →
      (⋂ n, U n) ∈ nhds (0 : G))
    (B : Set G) (hBb : Bornology.IsVonNBounded ℂ B) :
    ∃ (y : ℕ → G) (c : ℕ → ℝ), Bornology.IsVonNBounded ℂ (Set.range y) ∧
      (∀ n, 0 ≤ c n) ∧ Summable c ∧
      ∀ x ∈ B, ∃ a : ℕ → ℂ, (∀ n, ‖a n‖ ≤ c n) ∧
        HasSum (fun n => a n • y n) x := by sorry
