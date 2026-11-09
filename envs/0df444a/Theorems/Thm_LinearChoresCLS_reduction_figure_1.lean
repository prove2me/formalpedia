-- Prove2me | Theorems.Thm_LinearChoresCLS_reduction_figure_1
-- name    : LinearChoresCLS.reduction_figure_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:48:00.125724+00:00
-- url     : https://prove2.me/theorems/c55c1d7e-d790-4d06-8e76-820492d2d8cb
-- title:
--   The reduction (Figure 1, §7.1) — ε-quadratic-KKT reduces to linear chores CE
-- statement:
--   There are polynomial-time maps $f$ (the market construction $I\mapsto f(I)$) and $g$ (the decoder (7.3)) such that, for every instance $I=(A,c,\varepsilon)$ of the $\varepsilon$-quadratic-KKT problem, $f(I)$ is a valid linear chores market with strictly positive rational data, and for **every** exact rational competitive equilibrium $(p^\star,z^\star)$ of $f(I)$, $g(I,(p^\star,z^\star))$ is an $\varepsilon$-KKT point of $I$.
--
--   This is the hardness half of Theorem 1.1 in reduction form: it combines the construction, Lemma 7.1, Lemma 7.5, Lemma 7.6 and Proposition 4.1.
--
--   **Formalization Note** The reduction is the public Levin search reduction `CardinalMatching.SearchReduces` on Cook's machines, required to be correct for every answer.
--
--   Differences from the source:
--   - encoding: "both the market construction and solution recovery can be carried out in polynomial time" → SearchReduces epsQKKTSearch choresCESearch (polynomial-time instance and answer maps on Cook's machines, correct for every answer); reason: the standard formal notion of a polynomial-time search reduction, the one used by the public CLS class
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Section 3, Figure 1, p.8, and Section 7.1, p.38

import Mathlib
import Definitions.Def_LinearChoresCLS_EpsKKT
import Definitions.Def_LinearChoresCLS_ChoresSearch

open NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- **The reduction of Theorem 1.1** (arXiv:2611.06589, held version sha256 85d34a9e…, Section 3,
Figure 1, p.8, and Section 7.1, p.38): the ε-quadratic-KKT problem reduces to computing a
competitive equilibrium of a linear chores market. There are a polynomial-time instance map `f`
(the market construction `I ↦ f(I)`, with strictly positive rational data of polynomial encoding
length) and a polynomial-time answer map `g` (the decoder (7.3)) such that for every instance `I`,
`f(I)` is a valid market and, for **every** exact rational competitive equilibrium `(p⋆, z⋆)` of
`f(I)`, `g(I, (p⋆, z⋆))` is an ε-KKT point of `I`.

**Formalization Note.** The reduction is the public Levin search reduction
`CardinalMatching.SearchReduces` on Cook's machines; correctness is required for every answer. -/
theorem reduction_figure_1 : SearchReduces epsQKKTSearch choresCESearch := by sorry

end LinearChoresCLS
