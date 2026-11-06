-- Prove2me | Theorems.Thm_FourierRankQLB_lemma_4_7
-- name    : FourierRankQLB.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:44:55.196001+00:00
-- url     : https://prove2.me/theorems/337ab869-c967-4bdc-a470-62595b964725
-- title:
--   Lemma 4.7 — separation of the determinant components
-- statement:
--   Let $d\ge2$ be even, and let $P_\pm$, $E_\pm$ denote probability and expectation over $Q\sim\mu_{d,\pm}$ and an independent normalized random sign vector $v$. The statistic $Z(Q,v)=\sqrt{a_dd\,v^TA_Q^{-1}v}$ satisfies
--   $$
--   P_-\Bigl[Z\ge\frac1{\sqrt3}\Bigr]\ge\frac4{27},\qquad E_+[Z^2]\le\frac{2d\sqrt{a_d}}{\sqrt{1+a_d}}\le\sqrt2\,\alpha<\frac9{200}.
--   $$
--
--   So $Z$ tends to be larger on the reflection component, and one random objective carries a constant amount of information about $\det Q$.
--
--   Differences from the source:
--
--   - encoding: $P_\pm$, $E_\pm$ over $Q\sim\mu_{d,\pm}$ and an independent $v$ → an integral over $Q$ of the finite average `signAvg`; reason: independence with a uniform law on a finite set; same values
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Lemma 4.7, Eq. (46), p.28

import Mathlib
import Definitions.Def_FourierRankQLB_Zstat
import Definitions.Def_FourierRankQLB_signObj
import Definitions.Def_FourierRankQLB_signAvg
import Definitions.Def_FourierRankQLB_muPlus
import Definitions.Def_FourierRankQLB_muMinus
import Definitions.Def_FourierRankQLB_alpha

open MeasureTheory

namespace FourierRankQLB

/-- Lemma 4.7 (Separation of the determinant components), Eq. (46): for even `d ≥ 2`,
`P₋[Z ≥ 1/√3] ≥ 4/27` and `E₊[Z²] ≤ 2d√a_d/√(1 + a_d) ≤ √2 α < 9/200`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Lemma 4.7, Eq. (46), p. 28.

**Formalization Note.** `P_±` and `E_±` are over `Q ∼ μ_{d,±}` and an independent uniform sign vector:
an integral over `Q` of the finite average `signAvg`. A probability is the average of an indicator. -/
theorem lemma_4_7 {d : ℕ} (hd : 2 ≤ d) (hev : Even d) :
    4 / 27 ≤ ∫ Q, signAvg (fun σ => if 1 / √3 ≤ Zstat Q (signObj σ) then (1 : ℝ) else 0)
      ∂muMinus d ∧
    ∫ Q, signAvg (fun σ => Zstat Q (signObj σ) ^ 2) ∂muPlus d
      ≤ 2 * d * √(ad d) / √(1 + ad d) ∧
    2 * d * √(ad d) / √(1 + ad d) ≤ √2 * alpha ∧
    √2 * alpha < 9 / 200 := by sorry

end FourierRankQLB
