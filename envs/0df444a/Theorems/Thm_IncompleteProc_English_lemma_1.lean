-- Prove2me | Theorems.Thm_IncompleteProc_English_lemma_1
-- name    : IncompleteProc.English.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:37.659891+00:00
-- url     : https://prove2.me/theorems/f9598808-200c-49f4-a321-a8f4ef0fb086
-- title:
--   Lemma 1, p. 13 (PDF 14) — envelope formula (5) for incentive-compatible mechanisms; Uⁱ(c̄) ≥ 0 gives individual rationality
-- statement:
--   Let a direct mechanism be admissible and incentive compatible in the two-period procurement model, and let $U^i(c) = U^i(c, c)$ be supplier $i$'s profit from truthful reporting. Here $X^i_1(s)$ and $X^i_2(s, \omega)$ are his interim probabilities of supplying in periods 1 and 2. Then for every supplier $i$ and every $c \in [\underline c, \bar c]$,
--   $$U^i(c) = U^i(\bar c) + \int_c^{\bar c} \Big( X^i_1(s) + \int_\Omega Q\, k_c(s, \omega)\, X^i_2(s, \omega)\, dG(\omega) \Big)\, ds. \tag{5}$$
--   Moreover, if $U^i(\bar c) \ge 0$ for every $i$ (6), the mechanism is individually rational.
--
--   This is the envelope characterization of incentive compatibility. It pins down every type's profit from the allocation and the profit of the highest type, and it is the step that turns the buyer surplus into a virtual surplus.
--
--   **Formalization Note** The paper writes the integrand as $X^i_1(s)\big(1 + \int_\Omega Q k_c(s, \omega) X^i_2(s, \omega)\, dG\big)$, reading $X^i_2$ as the probability of supplying in period 2 conditional on supplying in period 1. The mission reads $x_2$ unconditionally, so the product $X^i_1 X^i_2$ becomes $X^i_2$. The standing assumptions (including the boundedness of $k$ that the proof uses) and Assumption 1 are hypotheses.
-- source:
--   Gretschko & Pollrich, Incomplete Contracts in Dynamic Procurement, ZEW Discussion Paper No. 19-040 (Sept. 2019; SSRN 3466701), p. 13 (PDF 14), Lemma 1, eqs. (5)–(6)

import Mathlib
import Definitions.Def_IncompleteProc_English_Model

namespace IncompleteProc.English

open MeasureTheory

/-- Lemma 1 (p. 13): for an admissible incentive-compatible direct mechanism, supplier `i`'s
truthful profit satisfies the envelope formula (5),
`Uⁱ(c) = Uⁱ(c̄) + ∫_c^{c̄} (X¹ᵢ(s) + ∫_Ω Q k_c(s, ω) X²ᵢ(s, ω) dG(ω)) ds`
(second-period allocation read unconditionally), and such a mechanism is individually rational if
`Uⁱ(c̄) ≥ 0` for all `i` (6). -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (E : Env Ω) (hS : E.Standing)
    (hA : E.Assumption1) (M : Mech E.n Ω) (hM : M.Admissible E) (hIC : M.IsIC E) :
    (∀ i, ∀ c ∈ Set.Icc E.clo E.chi,
      M.U E i c c = M.U E i E.chi E.chi +
        ∫ s in c..E.chi, (M.X1 E i s + ∫ ω, E.Q * E.kc s ω * M.X2 E i s ω ∂E.G)) ∧
    ((∀ i, 0 ≤ M.U E i E.chi E.chi) → M.IsIR E) := by sorry

end IncompleteProc.English
