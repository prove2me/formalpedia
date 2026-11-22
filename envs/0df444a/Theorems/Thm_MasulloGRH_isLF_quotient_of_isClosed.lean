-- Prove2me | Theorems.Thm_MasulloGRH_isLF_quotient_of_isClosed
-- name    : MasulloGRH.isLF_quotient_of_isClosed
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:01.281866+00:00
-- url     : https://prove2.me/theorems/9632c086-596c-46a2-bed4-926e54d5eb0b
-- title:
--   The quotient of an LF-space by a closed subspace is an LF-space
-- statement:
--   **Hausdorff quotients of LF-spaces are LF-spaces.** Let $E$ be an LF-space over $\mathbb C$ (Definition C.1.5.2 of the source): a Hausdorff locally convex space which is the locally convex inductive limit $E=\varinjlim E_k$ of a sequence of Fréchet spaces with injective continuous linear transition maps. Let $M\subset E$ be a closed linear subspace. Then the quotient
--   $$E/M,$$
--   with the quotient topology, is again an LF-space.
--
--   The source notes that a quotient of a *strict* LF-space need not be strict, which is one reason it works with general LF-spaces and their Open Mapping Theorem (Theorem C.1.5.5); the present statement is used in that way in the proof of Corollary C.1.5.13.
--
--   **Deviation from the source.** The source says "any quotient of an LF-space is an LF-space". Since an LF-space is Hausdorff by definition and $E/M$ is Hausdorff exactly when $M$ is closed, the statement is formalized for closed subspaces $M$.
--
--   **Formalization Note.** `MasulloGRH.IsLF` is the platform predicate; its steps are submodules of the space, each with its own Fréchet topology. The subspace is a `Submodule ℂ E` with closed carrier and `E ⧸ W` carries Mathlib's quotient topology. The formal statement asserts only that $E/M$ admits some defining sequence of Fréchet steps; it does not single one out.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 662-664, Example C.1.4.6(4) and Definition C.1.5.2 (LF-spaces, after A. Grothendieck, Topological Vector Spaces, Gordon and Breach, 1973, Def. 4 p. 146, as cited by the paper), p. 663 ('any quotient of an LF-space is an LF-space'), with Remark C.1.3.4, p. 660 (quotients of Fréchet spaces)

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex

open Topology

set_option autoImplicit false

namespace MasulloGRH

theorem isLF_quotient_of_isClosed (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsLF E) (W : Submodule ℂ E) (hW : IsClosed (W : Set E)) :
    IsLF (E ⧸ W) := by sorry

end MasulloGRH
