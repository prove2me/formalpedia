-- Prove2me | Theorems.Thm_HuangYin_lemma_3
-- name    : HuangYin.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:46:12.213738+00:00
-- url     : https://prove2.me/theorems/f7549170-9687-42be-b3bc-dfdde21e33a7
-- title:
--   Lemma 3 — optimal offering probabilities at $p_1=v_{HL}$, $p_2=v_L$ (corrected: $c_L\le v_{HL}$)
-- statement:
--   Assume $c_L\le v_{HL}$ and write $R=(v_{HL}-c_L)/(c_H-c_L)$. When $p_1=v_{HL}$ and $p_2=v_L$, the profit (2) over $(\xi_1,\xi_2)\in[0,1]^2$ is maximized by
--
--   1. $\xi_1=\frac{v_{HL}-c_L}{2(c_H-c_L)}$ and $\xi_2=0$ if $R<2$;
--   2. $\xi_1=1$ and $\xi_2=0$ if $R\ge2$.
--
--   The proof of Proposition 1 uses Lemma 3 to show that this price pair is never strictly optimal.
--
--   Differences from the source:
--
--   - correction: no sign condition on vHL − cL → hypothesis cL ≤ vHL; reason: false as printed: α = 0, vH = 3, vL = 1, cH = 6, cL = 5 satisfy every assumption of the paper and give (vHL − cL)/(cH − cL) = −3, so the prescribed ξ1 = −3/2 lies outside [0, 1]; cL ≤ vHL is exactly the condition that the prescribed ξ1 is nonnegative, and it is implied by the vL ≥ cL that the paper's proof uses (p. 30)
--   - encoding: K anecdotes per customer and a prior belief ξ0 (p. 8), with ξ0 = 0 from p. 9 on and K = 1 in §4 → the estimate (ξ0 + anecdote)/(K + 1) with K = 1, ξ0 = 0 built into `estimate`; the purchasing fractions derived from rule (1) in `demand`; reason: §4 and the result fix K = 1 and the paper fixes ξ0 = 0; the derived fractions are Lemma 1's γ's for K = 1 (1 at vL, ξ at vHL, 0 above vHL), so no instance changes
--   - reading: 'the optimal product offering decisions are' / 'it is optimal to use' → the stated choice is feasible and attains the maximum (`OptimalOffer`, `IsOptimal`), not that it is the unique maximizer; reason: Proposition 1 (iii) calls both transparent policies optimal when vH − cH = vL − cL, so optimality cannot mean uniqueness
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), Lemma 3, p. 12

import Mathlib
import Definitions.Def_HuangYin_OptimalOffer
import Definitions.Def_HuangYin_vHL

namespace HuangYin

/-- **Lemma 3: optimal offering probabilities at `p1 = vHL`, `p2 = vL`** (p. 12), corrected by
the hypothesis `cL ≤ vHL`.
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), Lemma 3, p. 12.

With `R = (vHL − cL)/(cH − cL)`: (i) if `R < 2`, `ξ1 = (vHL − cL)/(2(cH − cL))` and `ξ2 = 0` are
optimal; (ii) if `R ≥ 2`, `ξ1 = 1` and `ξ2 = 0` are optimal.

**Formalization Note.** The hypothesis `cL ≤ vHL` is a correction: without it (i) prescribes a
negative `ξ1` (α = 0, vH = 3, vL = 1, cH = 6, cL = 5 gives `ξ1 = −3/2`). "Optimal" means
attaining the maximum (`OptimalOffer`). -/
theorem lemma_3 (P : Params) (hcorr : P.cL ≤ vHL P) :
    ((vHL P - P.cL) / (P.cH - P.cL) < 2 →
      OptimalOffer P (vHL P) P.vL ((vHL P - P.cL) / (2 * (P.cH - P.cL))) 0) ∧
    (2 ≤ (vHL P - P.cL) / (P.cH - P.cL) →
      OptimalOffer P (vHL P) P.vL 1 0) := by sorry

end HuangYin
