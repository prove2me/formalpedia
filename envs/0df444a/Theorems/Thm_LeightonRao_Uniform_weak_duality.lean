-- Prove2me | Theorems.Thm_LeightonRao_Uniform_weak_duality
-- name    : LeightonRao.Uniform.weak_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:27:31.960637+00:00
-- url     : https://prove2.me/theorems/5dc6c018-3bee-4b53-b371-a098279d4a85
-- title:
--   §1.2, pp. 789–790 — the max-flow is upper bounded by the min-cut: f·|U||Ū| ≤ C(U, Ū) for a UMFP
-- statement:
--   Let a network on $n$ nodes carry the uniform multicommodity flow problem (demand one for every unordered pair of nodes). If a concurrent flow of value $\lambda$ exists, then for every nonempty proper subset $U\subset V$,
--   $$\lambda\,|U|\,|\bar U|\le C(U,\bar U).$$
--   The $|U|\,|\bar U|$ commodities separated by the cut each send $\lambda$ units across it, and all of that flow uses the capacity of the cut.
--
--   Dividing by $|U||\bar U|=D(U,\bar U)$ gives $f\le C(U,\bar U)/D(U,\bar U)$ for every cut, i.e. the max-flow is at most the min-cut — the upper half of Theorem 2.
--
--   **Formalization Note** Each unordered pair is two ordered commodities with demand $\tfrac12$ (footnote 2, p. 791).
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), pp. 789–790, §1.2 (cut argument for f ≤ C(U, Ū)/D(U, Ū)), with D(U, Ū) = |U||Ū| from §1.5, p. 792

import Definitions.Def_LeightonRao_Uniform_Flow

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.Uniform

/-- The cut inequality of §1.2 specialized to the ordered-pair encoding of a UMFP. -/
theorem weak_duality {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (f : V → V → V → V → ℝ) (lam : ℝ)
    (hf : IsConcurrentFlow N uniformDemand f lam)
    (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty) :
    lam * ((U.card : ℝ) * (Uᶜ.card : ℝ)) ≤ cutCap N U := by sorry

end LeightonRao.Uniform
