-- Prove2me | Theorems.Thm_MasulloGRH_nuclearFrechet_strongBidual_eval
-- name    : MasulloGRH.nuclearFrechet_strongBidual_eval
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:41:13.139498+00:00
-- url     : https://prove2.me/theorems/ba5385cd-c332-4121-83ee-dc142db5da64
-- title:
--   Nuclear Fréchet spaces are semi-reflexive
-- statement:
--   Let $E$ be a nuclear Fréchet space over $\mathbb C$ and $E'_\beta$ its strong dual (continuous linear functionals with the topology of uniform convergence on bounded subsets of $E$). Then every continuous linear functional $F$ on $E'_\beta$ is the evaluation at a point of $E$: there is $y\in E$ with
--
--   $$F(f)=f(y)\qquad\text{for all } f\in E'.$$
--
--   That is, $E$ is semi-reflexive. This holds because a nuclear Fréchet space is a Montel space (bounded sets are pre-compact, and closed bounded sets are complete, hence compact), and Montel spaces are reflexive (Example C.1.4.6(3)).
--
--   **Formalization Note** $E'_\beta$ is Mathlib's `StrongDual ℂ E` and its dual is `StrongDual ℂ (StrongDual ℂ E)`; nuclearity and the Fréchet property are the predicates of the definition file. Uniqueness of $y$ (which follows from Hahn–Banach) is not part of the statement.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Example C.1.4.6(3) and Lemma C.2.4.16 (nuclear spaces are Montel); Schaefer, Topological Vector Spaces, Ch. IV, 5.5 and 5.8

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem nuclearFrechet_strongBidual_eval (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (hN : IsNuclear E)
    (F : StrongDual ℂ (StrongDual ℂ E)) :
    ∃ y : E, ∀ f : StrongDual ℂ E, F f = f y := by sorry

end MasulloGRH
