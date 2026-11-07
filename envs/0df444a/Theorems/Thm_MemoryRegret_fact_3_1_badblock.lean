-- Prove2me | Theorems.Thm_MemoryRegret_fact_3_1_badblock
-- name    : MemoryRegret.fact_3_1_badblock
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:39:44.670073+00:00
-- url     : https://prove2.me/theorems/95c74313-790e-4ab2-a109-8a3cc0cad315
-- title:
--   Fact 3.1 — Bernoulli blocks are rarely unbalanced
-- statement:
--   Let $\varepsilon\in(0,\frac12)$, $r>1$ and $1\le m<1000/(\varepsilon^2r^2)$. For either bit $b$,
--   $$\Pr_{b^{(1)},\dots,b^{(m)}\sim\mathrm{Ber}(b,\frac12+\varepsilon)^m}\Bigl[\Bigl|\sum_ib^{(i)}-\frac m2\Bigr|\ge50r\sqrt m\Bigr]\le2^{-r^2}.$$
--
--   This bounds the chance that the truncated path stops because of a bad block.
--
--   Differences from the source:
--   - encoding: m < 1000/(ε²r²) → m·ε²·r² < 1000; reason: multiplicative form avoids x/0 = 0; the two forms agree for ε, r > 0
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), Fact 3.1, p.10

import Mathlib
import Definitions.Def_MemoryRegret_IsProbVec
import Definitions.Def_MemoryRegret_berBlock

namespace MemoryRegret

/-- **Fact 3.1 (Bernoulli blocks are rarely unbalanced).**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
Fact 3.1, p.10.

Let `ε ∈ (0, ½)`, `r > 1` and `1 ≤ m < 1000/(ε²r²)`. For either bit `b`, if
`b^{(1)}, …, b^{(m)}` are i.i.d. `Ber(b, ½ + ε)`, then
`Pr[|∑_i b^{(i)} − m/2| ≥ 50r√m] ≤ 2^{−r²}`.

**Formalization Note.** The event is `BadBlock m r`; the law of the block is `berBlock ε b`.
`m < 1000/(ε²r²)` is written `m·ε²·r² < 1000`. -/
theorem fact_3_1_badblock (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) (r : ℝ) (hr : 1 < r)
    (m : ℕ) (hm : 1 ≤ m) (hm' : (m : ℝ) * ε ^ 2 * r ^ 2 < 1000) (b : Bool) :
    wprob (berBlock (m := m) ε b) (· ∈ BadBlock m r) ≤ (2 : ℝ) ^ (-r ^ 2) := by sorry

end MemoryRegret
