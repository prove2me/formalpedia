-- Prove2me | Theorems.Thm_FuchsVdGraaf_eq_82
-- name    : FuchsVdGraaf.eq_82
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:14:32.024328+00:00
-- url     : https://prove2.me/theorems/2dd74fcd-f9c8-465f-bea9-6ac7c07b5cc8
-- title:
--   Eq. (82) — $2\min\{x,1-x\} \le H_2(x) \le 2\sqrt{x(1-x)}$
-- statement:
--   Let $H_2(x) = -x\log_2 x - (1-x)\log_2(1-x)$ be the binary entropy in bits. For every $x$ with $0\le x\le 1$,
--
--   $$
--   2\min\{x, 1-x\} \;\le\; H_2(x) \;\le\; 2\sqrt{x(1-x)} .
--   $$
--
--   These two elementary bounds (pictured in Figure 1 of the paper) convert statements about the Shannon distinguishability into statements about the probability of error (lower bound) and the Bhattacharyya coefficient (upper bound).
--
--   Differences from the source:
--   - reading: (82) states no domain → $0\le x\le 1$; reason: the paper uses the bound "for all r between 0 and 1" (p.18) and Figure 1 plots it on $[0,1]$, the domain of $H_2$.
--   - encoding: $\log$ in $H_2$ (base fixed by $H(T)=1$, p.15) → `WildeQIT.binaryEntropy` with `Real.logb 2`; reason: Lean convention, same function on $[0,1]$.
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, eq. (82), p.22; Figure 1, p.19; p.18

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, eq. (82), p.22 (also Figure 1, p.19, and
its use on p.18 "for all r between 0 and 1"): for `0 ≤ x ≤ 1`,
`2 min{x, 1 − x} ≤ H₂(x) ≤ 2 √(x(1 − x))`, with `H₂` the binary entropy in bits.

**Formalization Note.** `H₂` is the published `WildeQIT.binaryEntropy`
(`−x log₂ x − (1 − x) log₂ (1 − x)`, with `H₂(0) = H₂(1) = 0`). The domain `[0, 1]` is the one
the paper uses on p.18 and the range plotted in Figure 1. -/
theorem eq_82 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    2 * min x (1 - x) ≤ WildeQIT.binaryEntropy x ∧
      WildeQIT.binaryEntropy x ≤ 2 * Real.sqrt (x * (1 - x)) := by sorry

end FuchsVdGraaf
