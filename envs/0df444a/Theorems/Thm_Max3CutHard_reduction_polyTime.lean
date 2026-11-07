-- Prove2me | Theorems.Thm_Max3CutHard_reduction_polyTime
-- name    : Max3CutHard.reduction_polyTime
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:51:53.477502+00:00
-- url     : https://prove2.me/theorems/b9935b1a-6553-4b50-be8c-23836a56c437
-- title:
--   Section 2 — the reduction $\Phi\mapsto J(\Phi)$ is polynomial-time
-- statement:
--   There is a polynomial-time computable map $g$ on words such that for every encodable instance $\Phi$ of 3Lin($\mathbb Z_3$),
--
--   $$g(\mathrm{enc}(\Phi))=\mathrm{enc}(J_{\mathbb N}(\Phi)),$$
--
--   where $J_{\mathbb N}(\Phi)$ is the reduction graph for the family $(2E,N,N)$ as an integer-weighted multigraph and both encodings are the unary ones of the mission.
--
--   The source constructs $J(\Phi)$ explicitly; polynomial running time is what makes the composition with Theorem 2.1 an NP-hardness reduction.
--
--   Differences from the source:
--   - reading: the explicit construction of J(Φ), with no stated running time → ∃ g PolyTimeComputable with encMaxCut (Jnat Φ) = g (encLin Φ); reason: the NP-hardness of Theorem 1.1 needs the reduction to run in polynomial time; the construction is explicit and of polynomial size
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, The reduction, p.5

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_Max3CutHard_Jnat
import Definitions.Def_Max3CutHard_encLin
open OptInapprox.MaxCut

namespace Max3CutHard

/-- **The reduction is computable in polynomial time.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, The reduction, p.5:
"Given a role-separated `Φ` and a family, the graph `J = J(Φ)` (Fig. 2) has a vertex for every
variable of `Φ`, `k` global vertices, and for every equation `e` a copy of `I_{t_e}` scaled by
`λ_e`, whose primaries `p1, p2, p3` are identified with `u_e, w_e, w′_e`, whose global vertices
are identified with the global vertices of `J`, and whose auxiliary vertices are new."

**Formalization Note.** The paper does not state the running time; the explicit construction is
polynomial. Stated for the ℕ-weighted `Jnat` and the published unary `encMaxCut`, with
`CookPvsNP.PolyTimeComputable`. -/
theorem reduction_polyTime : ∃ g : List LinSym → List MCSym, CookPvsNP.PolyTimeComputable g ∧
    ∀ Φ : LinInst, encMaxCut (Jnat Φ) = g (encLin Φ) := by sorry

end Max3CutHard
