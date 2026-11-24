-- Prove2me | Theorems.Thm_LefebvreVariations_symmetric_group_three_realizable
-- name    : LefebvreVariations.symmetric_group_three_realizable
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:09:19.829366+00:00
-- url     : https://prove2.me/theorems/d69b096b-8814-4b1f-93a7-62f1b5f31ebd
-- title:
--   Lefebvre's variations, No. 11 — on a theme by Hilbert: the symmetric group $S_3$ is a Galois group over $\mathbb Q$
-- statement:
--   This is the symmetric group $S_3$ case of the inverse Galois problem over $\mathbb Q$.
--
--   There is a finite Galois extension $L/\mathbb Q$ with
--
--   $$
--   \mathrm{Gal}(L/\mathbb Q)\ \cong\ S_3 ,
--   $$
--
--   namely the splitting field $L=\mathbb Q(\sqrt[3]{2},\omega)$ of $X^3-2$, where $\omega$ is a primitive cube root of unity. The polynomial is irreducible because $2$ is not a cube in $\mathbb Q$, it has prime degree $3$, and it has exactly one real root, hence exactly two non-real ones; complex conjugation then acts as a transposition and the Galois group is all of $S_3$.
--
--   This is the smallest non-abelian instance of the inverse Galois problem, which asks whether every finite group occurs as a Galois group over $\mathbb Q$.
--
--   **Formalization Note** Realizability is the mission's `InverseGalois.IsRealizable ℚ G` with $G$ = `Equiv.Perm (Fin 3)`.
-- source:
--   Classical example of the splitting field of X^3 − 2 over ℚ, whose Galois group is S_3: D. S. Dummit and R. M. Foote, Abstract Algebra, 3rd ed., Wiley, 2004, Section 14.2. All symmetric groups occur over ℚ by D. Hilbert, Über die Irreducibilität ganzer rationaler Functionen mit ganzzahligen Coefficienten, J. reine angew. Math. 110 (1892), 104–129. Parent problem: InverseGalois.inverse_galois_problem (inverse Galois problem over ℚ), symmetric-group case.

import Definitions.Def_InverseGalois_realizability

set_option autoImplicit false

namespace LefebvreVariations
/-- `S₃ ≅ Gal(ℚ(∛2, ω)/ℚ)`, the splitting field of `X³ - 2` (irreducible, one real root). -/
theorem symmetric_group_three_realizable :
    InverseGalois.IsRealizable ℚ (Equiv.Perm (Fin 3)) := by
  sorry

end LefebvreVariations
