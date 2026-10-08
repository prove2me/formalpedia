-- Prove2me | Theorems.Thm_MulticlassDS_NatGap_prop42_pseudo_cube_good_complex
-- name    : MulticlassDS.NatGap.prop42_pseudo_cube_good_complex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:49:36.707206+00:00
-- url     : https://prove2.me/theorems/602a4f07-8844-4cdd-92bc-e60f46679ed8
-- title:
--   Proposition 42 (⇐), p. 28 — a (d+1)-dimensional pseudo-cube B gives a d-dimensional good complex C(B)
-- statement:
--   Let $B \subseteq \mathcal Y^{d+1}$ be a pseudo-cube of dimension $d + 1$. Then the complex $C(B)$, whose faces are the subsets of the sets $\{(y_i, i) : i \in [d+1]\}$ for $(y_1, \dots, y_{d+1}) \in B$, is a good simplicial complex of dimension $d$.
--
--   This is the converse half of the equivalence between pseudo-cubes and good complexes; together with the first half it shows that every concept class of this kind is a properly colored good complex and conversely.
--
--   **Formalization Note** The paper states the converse for a "$d$-dimensional pseudo-cube" and a "$(d-1)$-dimensional" complex; it is indexed here by $d + 1$ and $d$ to avoid natural-number subtraction (at $d = 0$ the page's complex would be "$(-1)$-dimensional"). The vertex type is $\mathcal Y \times$ `Fin (d + 1)`; only the vertices that occur in faces matter. Replacement is the version with a new vertex.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 28, Proposition 42, second sentence (pseudo-cube ⟹ good complex)

import Mathlib
import Definitions.Def_MulticlassDS_NatGap_Dimensions
import Definitions.Def_MulticlassDS_NatGap_Complexes

namespace MulticlassDS.NatGap

theorem prop42_pseudo_cube_good_complex {Y : Type*} (d : ℕ) (B : Set (Fin (d + 1) → Y))
    (hB : IsPseudoCube B) :
    IsGood (complexOf B) d := by sorry

end MulticlassDS.NatGap
