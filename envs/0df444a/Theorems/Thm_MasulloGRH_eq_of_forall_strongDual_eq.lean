-- Prove2me | Theorems.Thm_MasulloGRH_eq_of_forall_strongDual_eq
-- name    : MasulloGRH.eq_of_forall_strongDual_eq
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-21T00:25:46.019124+00:00
-- url     : https://prove2.me/theorems/bf6e699d-12f0-4590-97f6-75dbaefdd7da
-- title:
--   Continuous functionals separate points of a Hausdorff LCS
-- statement:
--   Let $G$ be a Hausdorff locally convex space over $\mathbb C$. If $x,z\in G$ satisfy $f(x)=f(z)$ for every continuous linear functional $f\in G'$, then $x=z$ (Hahn–Banach separation of points).
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), Appendix C — auxiliary step in the proof that a weak expansion yields a scalar (nuclear) expansion

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem eq_of_forall_strongDual_eq (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hL : IsHLCS G) (x z : G)
    (h : ∀ f : StrongDual ℂ G, f x = f z) : x = z := by sorry

end MasulloGRH
