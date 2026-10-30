-- Prove2me | Theorems.Thm_FuchsVdGraaf_proposition_5_44
-- name    : FuchsVdGraaf.proposition_5_44
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:15.980174+00:00
-- url     : https://prove2.me/theorems/f0b1d4d8-3aee-48a7-9e48-2ca98e4c9127
-- title:
--   Proposition 5, eq. (44) — $1 - H_2(\mathrm{PE}) \le \mathrm{SD} \le 1 - 2\,\mathrm{PE}$ (classical)
-- statement:
--   Let $p_0, p_1$ be probability distributions on a finite set, with probability of error $\mathrm{PE}(p_0,p_1)$ and Shannon distinguishability $\mathrm{SD}(p_0,p_1)$, and let $H_2$ be the binary entropy in bits. Then
--
--   $$
--   1 - H_2\big(\mathrm{PE}(p_0,p_1)\big) \;\le\; \mathrm{SD}(p_0,p_1) \;\le\; 1 - 2\,\mathrm{PE}(p_0,p_1) .
--   $$
--
--   The left inequality is the binary case of Fano's inequality; the right one compares the information gained from one sample with the error of the best guess.
--
--   Differences from the source:
--   - encoding: $\mathrm{SD}(p_0,p_1) = I(T;X)$ and $H_2$ with base-2 logarithms → `shannonDist` through the expansion (32) and `WildeQIT.binaryEntropy`, both with `Real.logb 2`; reason: (32) is the paper's own expansion of $I(T;X)$, same values.
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, Proposition 5, eq. (44), p.17

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsProbDist
import Definitions.Def_FuchsVdGraaf_errorProb
import Definitions.Def_FuchsVdGraaf_shannonDist
import Definitions.Def_WildeQIT_binaryEntropy

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, Proposition 5, eq. (44), p.17: for
probability distributions `p₀`, `p₁` on a finite set,
`1 − H₂(PE(p₀, p₁)) ≤ SD(p₀, p₁) ≤ 1 − 2 PE(p₀, p₁)`.

**Formalization Note.** `H₂` is `WildeQIT.binaryEntropy` (bits); `SD` is `shannonDist`, the
mutual information `I(T; X)` written through (32). -/
theorem proposition_5_44 {X : Type} [Fintype X] (p0 p1 : X → ℝ)
    (hp0 : IsProbDist p0) (hp1 : IsProbDist p1) :
    1 - WildeQIT.binaryEntropy (errorProb p0 p1) ≤ shannonDist p0 p1 ∧
      shannonDist p0 p1 ≤ 1 - 2 * errorProb p0 p1 := by sorry

end FuchsVdGraaf
