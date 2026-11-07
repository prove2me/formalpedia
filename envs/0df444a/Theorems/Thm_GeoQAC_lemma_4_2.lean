-- Prove2me | Theorems.Thm_GeoQAC_lemma_4_2
-- name    : GeoQAC.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:32:17.55065+00:00
-- url     : https://prove2.me/theorems/528cfdc7-953b-44a0-ac47-60c850d27d09
-- title:
--   Lemma 4.2 — Rosenthal's depth-2 $[m,\exp(O(m\log m))]$ approximate nekomata
-- statement:
--   (Rosenthal, Theorem 4.1 and Section 4.2.) For every $m\ge2$, there is a depth-2 $[m,\exp(O(m\log m))]$-2D-QAC circuit synthesizing a $3/4$-approximate $m$-nekomata.
--
--   Moreover its $m$ targets fill the left boundary column: target $i$ is at row $i$ of column $0$.
--
--   This is the base synthesis that the parity construction of Theorem 4.1(d) amplifies and converts.
--
--   Differences from the source:
--   - generalization: no target placement → the $m$ targets fill the left boundary column; reason: the proof of Theorem 4.1(d), p.31, uses "The synthesis circuit from Lemma 4.2 has its targets in the left boundary column"; the conclusion only gains a clause.
--   - encoding: $\exp(O(m\log m))$ → $\exp(C_1\,m\log m)$ with an absolute $C_1$ chosen before $m$ and the natural logarithm; reason: §2.1, p.9 (absolute constants; any fixed base of logarithm).
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Lemma 4.2, p.30 (citing Rosenthal 2021, Theorem 4.1 and Section 4.2); proof of Theorem 4.1(d), p.31

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_IsNekomataApprox

namespace GeoQAC

/-- **Lemma 4.2** ([Ros21, Theorem 4.1 and Section 4.2]; arXiv:2604.07178, version of 2026-11-03,
p.30). For every `m ≥ 2`, there is a depth-2 `[m, exp(O(m log m))]`-2D-QAC circuit synthesizing a
`3/4`-approximate `m`-nekomata.

**Formalization Note.**
* The `O(·)` constant `C₁` is absolute, chosen before `m`; `log` is the natural logarithm (p.9: any
  fixed base).
* Placement clause from the proof of Theorem 4.1(d), p.31: "The synthesis circuit from Lemma 4.2
  has its targets in the left boundary column". With `m` rows, the `m` targets fill column `0`:
  target `i` is at `(i, 0)`. This is a stronger conclusion than the printed lemma.
* Synthesis starts from `|0…0⟩` on the whole grid; depth `2` counts multi-qubit layers. -/
theorem lemma_4_2 : ∃ C₁ : ℝ, ∀ m : ℕ, 2 ≤ m →
    ∃ (h : ℕ) (C : QACCircuit (Pos m h) 2) (tgt : Fin m ↪ Pos m h),
      C.Is2D ∧ (h : ℝ) ≤ Real.exp (C₁ * m * Real.log m) ∧
      (∀ i, (tgt i).1 = i ∧ (tgt i).2.val = 0) ∧
      IsNekomataApprox (3 / 4) C tgt := by sorry

end GeoQAC
