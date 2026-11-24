-- Prove2me | Theorems.Thm_LefebvreVariations_symmetric_group_five_realizable
-- name    : LefebvreVariations.symmetric_group_five_realizable
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T21:56:41.06016+00:00
-- url     : https://prove2.me/theorems/991a955c-038d-4295-bf59-71cc078211c5
-- title:
--   Lefebvre's variations, No. 5 — on a theme by Hilbert: the symmetric group $S_5$ is a Galois group over $\mathbb Q$
-- statement:
--   This is the symmetric group $S_5$ case of the inverse Galois problem over $\mathbb Q$.
--
--   There is a finite Galois extension $L/\mathbb Q$ whose Galois group is isomorphic to the symmetric group on five letters:
--
--   $$
--   \mathrm{Gal}(L/\mathbb Q)\ \cong\ S_5 .
--   $$
--
--   A witness is the splitting field of $X^5-4X+2$. This polynomial is irreducible by Eisenstein's criterion at $2$, has prime degree $5$, and has exactly three real roots, hence exactly two non-real ones; an irreducible polynomial of prime degree $p$ over $\mathbb Q$ with exactly two non-real roots has Galois group $S_p$, because complex conjugation acts as a transposition and the group contains a $p$-cycle.
--
--   The inverse Galois problem asks whether every finite group is a Galois group over $\mathbb Q$. Symmetric groups were realized by Hilbert using his irreducibility theorem; $S_5$ is the first symmetric group that is not solvable, so this instance is also the classical witness for the unsolvability of the quintic by radicals.
--
--   **Formalization Note** Realizability is the mission's `InverseGalois.IsRealizable ℚ G`: a field $L$ with an algebra structure over $\mathbb Q$, `IsGalois ℚ L`, and a group isomorphism $G\simeq (L\simeq_{\mathbb Q} L)$. Here $G$ is `Equiv.Perm (Fin 5)`.
-- source:
--   D. Hilbert, Über die Irreducibilität ganzer rationaler Functionen mit ganzzahligen Coefficienten, J. reine angew. Math. 110 (1892), 104–129 (every symmetric group S_n is a Galois group over ℚ). The witness X^5 − 4X + 2 (irreducible of prime degree with exactly two non-real roots, hence Galois group S_5) follows the Abel–Ruffini development in Mathlib's Archive, Wiedijk100Theorems/AbelRuffini.lean (Freek Wiedijk's 100 theorems, no. 16). Parent problem: InverseGalois.inverse_galois_problem (inverse Galois problem over ℚ), symmetric-group case.

import Definitions.Def_InverseGalois_realizability

set_option autoImplicit false

namespace LefebvreVariations

/-- `S₅` is the Galois group over `ℚ` of the irreducible quintic `X⁵ - 4X + 2` (Eisenstein at 2,
three real roots, hence two non-real ones; Hilbert 1892, Dummit–Foote §14.6): the symmetric group
on five letters is realizable over `ℚ`. -/
theorem symmetric_group_five_realizable :
    InverseGalois.IsRealizable ℚ (Equiv.Perm (Fin 5)) := by
  sorry

end LefebvreVariations
