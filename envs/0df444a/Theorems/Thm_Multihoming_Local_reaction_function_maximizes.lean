-- Prove2me | Theorems.Thm_Multihoming_Local_reaction_function_maximizes
-- name    : Multihoming.Local.reaction_function_maximizes
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:31.1822+00:00
-- url     : https://prove2.me/theorems/2163ce0d-5eb2-4231-8267-c4d3d1cd3c0b
-- title:
--   (15), PDF p. 17 (printed p. 11) — the reaction function maximizes firm i's multihoming profit p·x_i^M(p, p_j)
-- statement:
--   Let $t>0$ and $0\le\mu<t$, and let $e_i,e_j$ be the exclusive features of goods $i$ and $j$. For a given rival price $p_j$, firm $i$'s profit from charging $p$ under the multihoming demand (14) is $p\,x_i^M(p,p_j)$. The reaction function
--
--   $$
--   p_i^M(p_j)=\frac{t\mu-\mu^2+te_i}{2t}+\mu\,\frac{p_j-e_j}{2t}
--   $$
--
--   of (15) maximizes this profit: for every real $p$,
--
--   $$
--   p\,x_i^M(p,p_j)\;\le\;p_i^M(p_j)\,x_i^M\big(p_i^M(p_j),p_j\big).
--   $$
--
--   This is the best-response step of the multihoming pricing game; the candidate equilibrium prices (16) are the fixed point of the two reaction functions.
--
--   **Formalization Note** The maximization is over all real prices $p$; nonnegativity of prices is not imposed, as on the page. The hypothesis $\mu<t$ is Assumption 1 (i); it makes $t^2-\mu^2>0$, so the profit is a strictly concave quadratic in $p$.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 17 (printed p. 11), (15)

import Mathlib
import Definitions.Def_Multihoming_Local_Model

namespace Multihoming.Local

/-- (15), PDF p. 17: the reaction function `reactM` maximizes firm i's profit
`p * demandM t μ ei ej p pj` over all real prices `p`, for every rival price `pj`. -/
theorem reaction_function_maximizes (t μ ei ej pj : ℝ) (ht : 0 < t) (hμ : 0 ≤ μ) (hμt : μ < t) :
    ∀ p : ℝ, p * demandM t μ ei ej p pj ≤
      reactM t μ ei ej pj * demandM t μ ei ej (reactM t μ ei ej pj) pj := by sorry

end Multihoming.Local
