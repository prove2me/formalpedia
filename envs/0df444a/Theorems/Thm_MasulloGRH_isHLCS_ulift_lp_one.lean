-- Prove2me | Theorems.Thm_MasulloGRH_isHLCS_ulift_lp_one
-- name    : MasulloGRH.isHLCS_ulift_lp_one
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:17:43.19981+00:00
-- url     : https://prove2.me/theorems/4b443e4c-07bf-4111-a772-c6416acd436e
-- title:
--   The sequence space $\ell^1$ is a Hausdorff locally convex space
-- statement:
--   The Banach space
--
--   $$\ell^1=\Big\{(a_n)_{n\ge0}\in\mathbb C^{\mathbb N} : \sum_{n\ge0}|a_n|<\infty\Big\},\qquad \|a\|_1=\sum_{n\ge0}|a_n|,$$
--
--   with its norm topology, is a Hausdorff locally convex space: its topology is defined by a family of seminorms (for instance the single norm $\|\cdot\|_1$) and it is Hausdorff.
--
--   This is the test space in Grothendieck's characterization of nuclearity through the tensor product $E\otimes\ell^1$: applying the definition of nuclearity of $E$ to $F=\ell^1$ requires knowing that $\ell^1$ is an admissible Hausdorff locally convex space.
--
--   **Formalization Note** The predicate `IsHLCS` of the definition file quantifies over index types in the universe of the space, and nuclearity of a space `E : Type u` only tests spaces in universe `u`; therefore $\ell^1$ (Mathlib's `lp (fun _ : ℕ => ℂ) 1`, in `Type`) is lifted to an arbitrary universe `u` with `ULift`, carrying the transported group, module and topology structures.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Definition C.2.4.1 and Lemma C.2.4.10; Grothendieck's ℓ¹-criterion for nuclearity, cf. Schaefer, Topological Vector Spaces, Ch. III, §7 and Pietsch, Nuclear Locally Convex Spaces, Ch. 4

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

universe u

theorem isHLCS_ulift_lp_one : IsHLCS (ULift.{u} (lp (fun _ : ℕ => ℂ) 1)) := by sorry

end MasulloGRH
