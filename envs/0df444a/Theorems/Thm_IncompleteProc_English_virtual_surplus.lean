-- Prove2me | Theorems.Thm_IncompleteProc_English_virtual_surplus
-- name    : IncompleteProc.English.virtual_surplus
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:46.366987+00:00
-- url     : https://prove2.me/theorems/ae15d211-02dc-4cf8-83f0-a457e0e2c99d
-- title:
--   Proof of Proposition 1, p. 14 (PDF 15) — buyer surplus of an IC mechanism equals expected virtual surplus minus Σᵢ Uⁱ(c̄)
-- statement:
--   Let a direct mechanism be admissible and incentive compatible, with allocation $x_1, x_2$, transfers $t$ and truthful profits $U^i$. Let $C = (c^1, \dots, c^n)$ have the i.i.d. law with density $f$. Then its buyer surplus equals the expected virtual surplus minus the profits of the highest cost types:
--   $$\mathbb E\Big[\sum_{i=1}^n \Big(R x^i_1(C) + \int_\Omega Q R\, x^i_2(C, \omega)\, dG - t^i(C)\Big)\Big] = \mathbb E\Big[\sum_{i=1}^n \Big( x^i_1(C)\big(R - \Psi_1(c^i)\big) + \int_\Omega Q\, x^i_2(C, \omega)\big(R - \Psi_2(c^i, \omega)\big)\, dG(\omega) \Big)\Big] - \sum_{i=1}^n U^i(\bar c).$$
--
--   The identity reduces the buyer's problem to pointwise maximization of the virtual surplus, which is how the optimal allocation of Proposition 1 is found.
--
--   **Formalization Note** The paper's display omits the term $-\sum_i U^i(\bar c)$, which is zero for the optimal mechanism; the general identity needs it. As in Lemma 1, $x_2$ is read unconditionally, so the paper's $x^i_1 \cdot x^i_2$ in the period-2 term is $x^i_2$ here.
-- source:
--   Gretschko & Pollrich, Incomplete Contracts in Dynamic Procurement, ZEW Discussion Paper No. 19-040 (Sept. 2019; SSRN 3466701), p. 14 (PDF 15), proof of Proposition 1, display after Lemma 1

import Mathlib
import Definitions.Def_IncompleteProc_English_Model

namespace IncompleteProc.English

open MeasureTheory

/-- The virtual-surplus identity of the proof of Proposition 1 (p. 14): the buyer surplus of an
admissible incentive-compatible direct mechanism equals the expected virtual surplus
`E[∑ᵢ (x¹ᵢ (R − Ψ₁(cⁱ)) + ∫_Ω Q x²ᵢ(ω) (R − Ψ₂(cⁱ, ω)) dG(ω))]` minus the profits `∑ᵢ Uⁱ(c̄)` of
the highest types (second-period allocation read unconditionally). -/
theorem virtual_surplus {Ω : Type*} [MeasurableSpace Ω] (E : Env Ω) (hS : E.Standing)
    (hA : E.Assumption1) (M : Mech E.n Ω) (hM : M.Admissible E) (hIC : M.IsIC E) :
    M.buyerSurplus E =
      (∫ C, ∑ i, (M.x1 C i * (E.R - E.Psi1 (C i)) +
          ∫ ω, E.Q * M.x2 C ω i * (E.R - E.Psi2 (C i) ω) ∂E.G) ∂E.profileLaw) -
        ∑ i, M.U E i E.chi E.chi := by sorry

end IncompleteProc.English
