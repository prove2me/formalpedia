-- Prove2me | Theorems.Thm_FuchsVdGraaf_proposition_5_45
-- name    : FuchsVdGraaf.proposition_5_45
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:07.674184+00:00
-- url     : https://prove2.me/theorems/e624eee0-d265-409e-bd33-9a5bb50c3a3e
-- title:
--   Proposition 5, eq. (45) (corrected: reads $\sqrt{1-B^2}$) — $1 - B \le \mathrm{SD} \le 1 - H_2\big(\tfrac12 - \tfrac12\sqrt{1-B^2}\big)$ (classical)
-- statement:
--   Let $p_0, p_1$ be probability distributions on a finite set, with Bhattacharyya coefficient $B = B(p_0,p_1)$ and Shannon distinguishability $\mathrm{SD}(p_0,p_1)$, and let $H_2$ be the binary entropy in bits. Then
--
--   $$
--   1 - B \;\le\; \mathrm{SD}(p_0,p_1) \;\le\; 1 - H_2\Big(\tfrac12 - \tfrac12\sqrt{1 - B^2}\Big) .
--   $$
--
--   These bounds tie the information-theoretic measure $\mathrm{SD}$ to the overlap $B$, which (in the quantum case) has a closed formula while $\mathrm{SD}$ does not.
--
--   The printed display (45) has $\sqrt{1 - B}$ in place of $\sqrt{1 - B^2}$. The paper's own proof ends at (72) with $\sqrt{1-(B(p_0,p_1))^2}$, and the printed form is false: for $p_0 = (1, 0)$ and $p_1 = (\tfrac12,\tfrac12)$ one has $B = 1/\sqrt2$ and $\mathrm{SD} = 0.3113\ldots$, while $1 - H_2\big(\tfrac12 - \tfrac12\sqrt{1 - 1/\sqrt2}\big) = 0.2230\ldots$. With the square the right side is $0.3991\ldots$.
--
--   Differences from the source:
--   - correction: printed (45) "$1 - H_2(\tfrac12 - \tfrac12\sqrt{1 - B(p_0,p_1)})$" → $1 - H_2(\tfrac12 - \tfrac12\sqrt{1 - B(p_0,p_1)^2})$; reason: the printed form fails for $p_0 = (1,0)$, $p_1 = (\tfrac12,\tfrac12)$ ($\mathrm{SD} = 0.3113 > 0.2230$), and the proof's last line (72) has the square.
--   - encoding: $\mathrm{SD} = I(T;X)$ and $H_2$ with base-2 logarithms → `shannonDist` through (32) and `WildeQIT.binaryEntropy`, `Real.logb 2`; reason: the paper's own expansion, same values.
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, Proposition 5, eq. (45), p.17; proof eqs. (65)-(72), pp.18-19

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsProbDist
import Definitions.Def_FuchsVdGraaf_bhattacharyya
import Definitions.Def_FuchsVdGraaf_shannonDist
import Definitions.Def_WildeQIT_binaryEntropy

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, Proposition 5, eq. (45), p.17, **as
corrected**: for probability distributions `p₀`, `p₁` on a finite set,
`1 − B(p₀, p₁) ≤ SD(p₀, p₁) ≤ 1 − H₂(½ − ½ √(1 − B(p₀, p₁)²))`.

**Correction.** The printed (45) reads `√(1 − B(p₀, p₁))` without the square. The paper's own
proof ends at (72), p.19, with `√(1 − (B(p₀, p₁))²)`, and the printed form is false:
`p₀ = (1, 0)`, `p₁ = (½, ½)` give `B = 1/√2`, `SD = 0.3113…`, while the printed right side is
`1 − H₂(½ − ½√(1 − 1/√2)) = 0.2230…`. With the square the bound is `0.3991…`.

**Formalization Note.** `H₂` is `WildeQIT.binaryEntropy` (bits); `SD` is `shannonDist`. -/
theorem proposition_5_45 {X : Type} [Fintype X] (p0 p1 : X → ℝ)
    (hp0 : IsProbDist p0) (hp1 : IsProbDist p1) :
    1 - bhattacharyya p0 p1 ≤ shannonDist p0 p1 ∧
      shannonDist p0 p1 ≤ 1 - WildeQIT.binaryEntropy
        (1 / 2 - 1 / 2 * Real.sqrt (1 - bhattacharyya p0 p1 ^ 2)) := by sorry

end FuchsVdGraaf
