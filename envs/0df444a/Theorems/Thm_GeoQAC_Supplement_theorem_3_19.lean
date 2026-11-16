-- Prove2me | Theorems.Thm_GeoQAC_Supplement_theorem_3_19
-- name    : GeoQAC.Supplement.theorem_3_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:24:05.19191+00:00
-- url     : https://prove2.me/theorems/d79253f7-7b52-4430-ba53-dccd31b982a7
-- title:
--   Theorem 3.19 — width lower bound for exact MAJORITY
-- statement:
--   For every depth $d\ge1$ there is a constant $c>0$ such that every depth-$d$ $[w,h]$-2D-QAC circuit computing $\mathrm{MAJ}_n(x)=\mathbf 1\{|x|>n/2\}$ exactly from product ancillas, with inputs and output anywhere, has
--   $$
--   c\,n^{1/(12d+2)}\le w .
--   $$
--
--   Majority has average sensitivity only $\Theta(\sqrt n)$, so the average-sensitivity bound alone gives nothing; the bound comes from the second moment of the sensitivity.
--
--   Differences from the source:
--   - encoding: w = Ω(n^{1/(12d+2)}) for fixed d → ∀ d ∃ c > 0 with the bound for every n; reason: for fixed d a bound for n ≥ N extends to every n by shrinking c, since w ≥ 1 whenever n ≥ 1; same encoding as the base mission's Theorem 3.16
--   - encoding: product ancillas (§3.5) → any product of one-qubit unit vectors (published GeoQAC.ComputesExactly); reason: the paper's own convention for §3.5; |0^a⟩ is the special case
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Theorem 3.19, p.27

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_ComputesExactly
import Definitions.Def_GeoQAC_Supplement_hammingWeight

namespace GeoQAC.Supplement

open GeoQAC

/-- **Theorem 3.19** (Dong, Ou, Yao, arXiv:2604.07178, version of 2026-11-03, p.27). "For fixed depth
`d ≥ 1`, exact computation of `MAJ_n` requires `w = Ω(n^{1/(12d+2)})`."

**Formalization Note.**
* "For fixed depth": `∀ d ∃ c`; `c` may depend on `d` but not on `n`, the grid, the placement or the
  ancillas. The bound is stated for every `n` (for fixed `d`, a bound for large `n` extends to every
  `n` by shrinking `c`, since `w ≥ 1` once `n ≥ 1`), as in the base mission's encoding of Theorem 3.16.
* `MAJ_n(x) = 1{|x| > n/2}` (p.27); exact computation from product ancillas (§3.5, p.26) is the
  published `GeoQAC.ComputesExactly`. Real exponent `1/(12d+2)`. -/
theorem theorem_3_19 : ∀ d : ℕ, 1 ≤ d → ∃ c : ℝ, 0 < c ∧
    ∀ (n w h : ℕ) (C : QACCircuit (Pos w h) d) (inp : Fin n ↪ Pos w h)
      (anc : Pos w h → Bool → ℂ) (out : Pos w h),
      C.Is2D → ComputesExactly C inp anc out (majFn n) →
        c * (n : ℝ) ^ ((1 : ℝ) / (12 * (d : ℝ) + 2)) ≤ w := by sorry

end GeoQAC.Supplement
