-- Prove2me | Theorems.Thm_MasulloGRH_elemSchwartz_frechet_nuclear_montel
-- name    : MasulloGRH.elemSchwartz_frechet_nuclear_montel
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-21T03:19:33.671897+00:00
-- url     : https://prove2.me/theorems/390e8a3c-af9f-4c1b-bc6c-179d248c94ca
-- title:
--   Lemmas D.1.3.5(2) and D.1.3.7(3) — $\mathcal S(\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F)$ is a nuclear Montel Fréchet space
-- statement:
--   Let $A=\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ be an elementary abelian Lie group, with $F$ a finite abelian group, and let $\mathcal S(A)$ be the space of smooth functions of rapid decay on $A$ with its seminorm topology. A Hausdorff locally convex space is **complete** if every Cauchy net converges, **nuclear** if for every Hausdorff locally convex space $F$ the projective and injective topologies on $E\otimes F$ coincide, **reflexive** if the canonical map $E\to(E'_\beta)'_\beta$ into the strong bidual is a topological isomorphism, and **Montel** if it is reflexive and every closed bounded subset is compact. $E'_\beta$ is the **strong dual**: the continuous dual with the topology of uniform convergence on bounded sets.
--
--   Then:
--
--   1. $\mathcal S(A)$ is a Fréchet space.
--   2. $\mathcal S(A)$ is nuclear and Montel, and it is barrelled.
--   3. The strong dual $\mathcal S(A)'_\beta$ is complete, nuclear, Montel and barrelled.
--
--   The general Schwartz–Bruhat space $\mathcal S(G)$ is an inductive limit of spaces of this form, and inherits its properties from them.
--
--   **Formalization Note** $F=\prod_{i<s}\mathbb Z/d_i$ with all $d_i\neq0$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.1.3, Lemma D.1.3.5(2), p. 752, and Lemma D.1.3.7 (Nuclearity in the case of elementary abelian Lie groups), part (3), p. 753

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

namespace MasulloGRH

theorem elemSchwartz_frechet_nuclear_montel (m n r s : ℕ) (d : Fin s → ℕ) (hd : ∀ i, d i ≠ 0) :
    IsFrechet (ElemSchwartz m n r s d) ∧
    IsNuclear (ElemSchwartz m n r s d) ∧ IsMontel (ElemSchwartz m n r s d) ∧
    BarrelledSpace ℂ (ElemSchwartz m n r s d) ∧
    IsCompleteTVS (StrongDual ℂ (ElemSchwartz m n r s d)) ∧
    IsNuclear (StrongDual ℂ (ElemSchwartz m n r s d)) ∧
    IsMontel (StrongDual ℂ (ElemSchwartz m n r s d)) ∧
    BarrelledSpace ℂ (StrongDual ℂ (ElemSchwartz m n r s d)) := by sorry

end MasulloGRH
