-- Prove2me | Theorems.Thm_IncompleteProc_English_english_surplus_eq_optimal
-- name    : IncompleteProc.English.english_surplus_eq_optimal
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-31T18:43:52.728761+00:00
-- url     : https://prove2.me/theorems/42ea28e9-58db-47a8-985c-b9f21bfb2950
-- title:
--   Proof of Proposition 3, p. 19 — the English-auction buyer surplus equals that of the optimal mechanism of Proposition 1
-- statement:
--   Consider the two-period procurement model of Gretschko and Pollrich with $n$ suppliers whose first-period costs $c^1,\dots,c^n$ are i.i.d. with density $f$ on $[\underline c,\bar c]$, second-period cost $k(c,\omega)$ in state $\omega\sim G$, relative second-period quantity $Q$ and value $R$, under the standing assumptions and Assumption 1.
--
--   In the English auction with reserve price $r^\star=c^\star_1$ and truthful exit, the lowest-cost supplier $i$ wins whenever $c^i\le c^\star_1$, at the price $p_1=\min\{c^\star_1,\min_{j\ne i}c^j\}$. In period 2 the buyer offers
--   $$p_2(\omega,p_1)=\min\{k(p_1,\omega),\,k(c^\star_2(\omega),\omega)\},$$
--   which the winner accepts iff $p_2(\omega,p_1)\ge k(c^i,\omega)$. Write $\mathrm{BS}^{\mathrm{English}}$ for the buyer's expected surplus
--   $$\mathrm{BS}^{\mathrm{English}}=\mathbb E\Big[\sum_i \mathbf 1\{i\text{ wins}\}\Big(R-p_1+\int_\Omega \mathbf 1\{\text{accept}\}\,Q\,(R-p_2(\omega,p_1))\,dG(\omega)\Big)\Big].$$
--
--   Let $(x^\star,t^\star)$ be the direct mechanism of Proposition 1: allocation (3)–(4) (the lowest-cost supplier supplies in period 1 iff $c^i\le c^\star_1$, and in period 2 in state $\omega$ iff moreover $k(c^i,\omega)\le k(c^\star_2(\omega),\omega)$), with transfers $t^i(c)=T(c^i)$, where for $c\le c^\star_1$
--   $$T(c)=H(c)\Big(c+\int_{\Omega(c)}Qk(c,\omega)\,dG\Big)+\int_c^{c^\star_1}H(s)\Big(1+Q\int_{\Omega(s)}k_c(s,\omega)\,dG\Big)ds,\qquad H(c)=(1-F(c))^{n-1},$$
--   and $T(c)=0$ for $c>c^\star_1$. Then
--   $$\mathrm{BS}^{\mathrm{English}}=\mathrm{BS}(x^\star,t^\star).$$
--
--   Combined with Proposition 1 (optimality of $(x^\star,t^\star)$), this is the last step of Proposition 3: the English auction followed by the take-it-or-leave-it offer attains the maximal complete-contract buyer surplus.
--
--   **Formalization Note** The English-auction surplus is computed directly from the auction outcome (winner, price, offer and acceptance), with ties broken in favour of the lowest index (a probability-zero event); the right-hand side is the buyer surplus of `Env.optMech` from the model definition.
-- source:
--   Gretschko & Pollrich, Incomplete Contracts in Dynamic Procurement, ZEW Discussion Paper No. 19-040 (Sept. 2019; SSRN 3466701), pp. 18–19 (PDF 19–20), proof of Proposition 3, final sentence ('... and thus the buyer surplus in the English auction coincides with the maximal buyer surplus'); transfer rule T(c) from the proof of Proposition 1, p. 15 (PDF 16)

import Mathlib
import Definitions.Def_IncompleteProc_English_Model
import Definitions.Def_IncompleteProc_English_Auction

namespace IncompleteProc.English

open MeasureTheory

/-- Proof of Proposition 3 (p. 19, PDF 20): the buyer's expected surplus in the English auction
with reserve `c⋆₁` followed by the take-it-or-leave-it offer `p₂(ω, p₁) = min{k(p₁, ω), k(c⋆₂(ω), ω)}`
(truthful exit, the winner accepts iff `p₂ ≥ k(cⁱ, ω)`) coincides with the buyer surplus of the
optimal direct mechanism of Proposition 1 (allocation (3)–(4), transfers `tⁱ(C) = T(cⁱ)` of p. 15). -/
theorem english_surplus_eq_optimal {Ω : Type*} [MeasurableSpace Ω] (E : Env Ω) (hS : E.Standing)
    (hA : E.Assumption1) :
    E.englishSurplus = E.optMech.buyerSurplus E := by sorry

end IncompleteProc.English
