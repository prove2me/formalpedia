-- Prove2me | Theorems.Thm_Multihoming_Hump_reaction_maximizes
-- name    : Multihoming.Hump.reaction_maximizes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:39.772428+00:00
-- url     : https://prove2.me/theorems/48ea1e55-758b-47ec-b5b0-c57304541fff
-- title:
--   (15), PDF p. 17 (printed p. 11) — the reaction function maximizes firm i's profit pᵢxᵢᴹ(pᵢ, pⱼ)
-- statement:
--   Let $t>0$ be the mismatch cost and $0\le\mu<t$ the network-effect strength, and let both goods have $e$ exclusive features. For a rival price $p_j$, firm $i$'s profit at own price $p$ is $p\,x_i^M(p,p_j)$, with $x_i^M$ the multihoming demand (14). The reaction function (15),
--   $$p_i^M(p_j)=\frac{t\mu-\mu^2+te}{2t}+\mu\,\frac{p_j-e}{2t},$$
--   maximizes this profit over all real prices:
--   $$p\,x_i^M(p,p_j)\;\le\;p_i^M(p_j)\,x_i^M\big(p_i^M(p_j),p_j\big)\qquad\text{for every } p\in\mathbb R.$$
--
--   This is the paper's derivation of (15) from $\max_{p_i} p_i x_i$; it ties the reaction function to the demand model.
--
--   **Formalization Note** Stated for symmetric exclusive features $e_i=e_j=e$, the case Proposition 3 concerns. The hypothesis $\mu<t$ is Assumption 1(i); it makes $t^2-\mu^2>0$.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 17 (printed p. 11), (14)–(15)

import Mathlib
import Definitions.Def_Multihoming_Hump_Model

namespace Multihoming.Hump

/-- (15), PDF p. 17: for 0 ≤ μ < t, the reaction function maximizes firm i's profit
p · xᵢᴹ(p, pⱼ) over all real prices p. -/
theorem reaction_maximizes (t μ e pj : ℝ) (ht : 0 < t) (hμ0 : 0 ≤ μ) (hμt : μ < t) :
    ∀ p : ℝ, p * Multihoming.Thresholds.demandM t μ e p pj ≤
      Multihoming.Thresholds.reactM t μ e pj * Multihoming.Thresholds.demandM t μ e (Multihoming.Thresholds.reactM t μ e pj) pj := by sorry

end Multihoming.Hump
