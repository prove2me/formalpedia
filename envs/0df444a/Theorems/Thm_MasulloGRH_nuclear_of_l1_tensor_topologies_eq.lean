-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_of_l1_tensor_topologies_eq
-- name    : MasulloGRH.nuclear_of_l1_tensor_topologies_eq
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-20T22:50:12.56135+00:00
-- url     : https://prove2.me/theorems/e739e1ea-1901-411d-a69f-b5a095f04196
-- title:
--   Grothendieck’s nuclearity criterion with the single test space ℓ¹
-- statement:
--   Let $E$ be a Hausdorff locally convex complex vector space, and let $L=\ell^1(\mathbb N,\mathbb C)$ with its usual norm topology. If the projective and injective locally convex topologies on the algebraic tensor product $E\otimes L$ coincide, then $E$ is nuclear.
--
--   The hypothesis uses one fixed Banach space. The conclusion asserts equality of the two tensor topologies when $L$ is replaced by any Hausdorff locally convex complex vector space.
--
--   **Formalization Note** The test space is Mathlib’s complex sequence space with exponent $1$, lifted to the universe of $E$. The tensor topologies are those in Definition C.2.4.1.
-- source:
--   A. Grothendieck, Produits tensoriels topologiques et espaces nucléaires, Séminaire Bourbaki, exposé 69 (1952), §2.1, Theorem 3(a)–(b), p. 196, https://www.numdam.org/item/SB_1951-1954__2__193_0.pdf#page=5. Compare Masullo, The Music of the Primes, 20 November 2026 draft, Theorem C.2.4.2, p. 685, for the characterization by Banach test spaces.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH

universe u

theorem MasulloGRH.nuclear_of_l1_tensor_topologies_eq (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (ht : projTensorTopology E (ULift.{u} (lp (fun _ : ℕ => ℂ) 1)) =
      epsTensorTopology E (ULift.{u} (lp (fun _ : ℕ => ℂ) 1))) : IsNuclear E := by sorry
