-- Prove2me | Theorems.Thm_LpBallVI_Affine_lemma_2_3
-- name    : LpBallVI.Affine.lemma_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:11:21.879933+00:00
-- url     : https://prove2.me/theorems/6e6d835e-2b93-4f10-b025-d084421c2a3a
-- title:
--   Lemma 2.3 — an ε-approximate fixed point of T (ε ≤ 1/32) rounds to a PureCircuit solution
-- statement:
--   Let $I$ be a well-formed PureCircuit instance with $n$ nodes and $T : \mathbb R^n \to [0,1]^n$ its threshold operator, $T_v(x) = \phi_v(s_v(x))$. Let $0 \le \varepsilon \le 1/32$ and $x \in \mathbb R^n$ with $\|x - T(x)\|_\infty \le \varepsilon$. Then the assignment
--   $$g(v) = \begin{cases} 0 & x_v \le 1/8 \\ 1 & x_v \ge 7/8 \\ \bot & 1/8 < x_v < 7/8\end{cases}$$
--   is a solution of $I$. This decodes approximate fixed points of $T$, which the reduction produces, into PureCircuit solutions.
--
--   Differences from the source:
--   - encoding: ‖x − T(x)‖_∞ ≤ ϵ for x ∈ ℝ^n → |x_v − T_v(x)| ≤ ε for every node v, x : Fin n → ℝ; reason: the max norm written coordinatewise
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 14, Lemma 2.3

import Mathlib
import Definitions.Def_LpBallVI_Affine_PureCircuit

namespace LpBallVI.Affine

/-- **Lemma 2.3**, p. 14: for `0 ≤ ε ≤ 1/32`, if `x ∈ ℝⁿ` satisfies `‖x − T(x)‖_∞ ≤ ε`, then the
rounding `g(v) = 0` (`x_v ≤ 1/8`), `1` (`x_v ≥ 7/8`), `⊥` (otherwise) is a solution of the
`PureCircuit` instance. -/
theorem lemma_2_3 (I : PCInst) (hI : I.WellFormed) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 32)
    (x : Fin I.n → ℝ) (hx : ∀ v, |x v - I.T x v| ≤ ε) :
    I.IsSolution (roundAssign x) := by sorry

end LpBallVI.Affine
