-- Prove2me | Theorems.Thm_MasulloGRH_schwartz_space_euclidean_nuclear
-- name    : MasulloGRH.schwartz_space_euclidean_nuclear
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-21T03:46:21.182872+00:00
-- url     : https://prove2.me/theorems/2cf827c4-35bd-4680-b7bb-73ac2c986c94
-- title:
--   Proposition 2.1.1.6 — $\mathcal S(\mathbb R^m)$ is a nuclear, reflexive Fréchet space
-- statement:
--   Let $m\ge0$ and let $\mathcal S(\mathbb R^m)$ be the Schwartz space of smooth rapidly decreasing complex functions on $\mathbb R^m$, with its usual locally convex topology. A Hausdorff locally convex space is **complete** if every Cauchy net converges, **nuclear** if for every Hausdorff locally convex space $F$ the projective and injective topologies on $E\otimes F$ coincide, **reflexive** if the canonical map $E\to(E'_\beta)'_\beta$ into the strong bidual is a topological isomorphism, and **Montel** if it is reflexive and every closed bounded subset is compact. $E'_\beta$ is the **strong dual**: the continuous dual with the topology of uniform convergence on bounded sets.
--
--   Then:
--
--   1. $\mathcal S(\mathbb R^m)$ is nuclear, a Fréchet space, and reflexive.
--   2. The strong dual $\mathcal S(\mathbb R^m)'_\beta$, the space of tempered distributions, is complete, nuclear and Montel.
--
--   These are the properties of the Archimedean factor of the Schwartz–Bruhat spaces on adeles.
--
--   **Formalization Note** $\mathcal S(\mathbb R^m)$ is Mathlib's Schwartz space on the Euclidean space of dimension $m$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Chapter 2, §2.1.1, Proposition 2.1.1.6, p. 61 (the space S(R^m): Definition 2.1.1.4, pp. 60–61)

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

namespace MasulloGRH

theorem schwartz_space_euclidean_nuclear (m : ℕ) :
    IsNuclear (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) ∧
    IsFrechet (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) ∧
    IsReflexive (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) ∧
    IsCompleteTVS (StrongDual ℂ (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ)) ∧
    IsNuclear (StrongDual ℂ (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ)) ∧
    IsMontel (StrongDual ℂ (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ)) := by sorry

end MasulloGRH
