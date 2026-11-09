-- Prove2me | Theorems.Thm_NadlerCLS_lemma_C_6
-- name    : NadlerCLS.lemma_C_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:06:23.691209+00:00
-- url     : https://prove2.me/theorems/1f285598-2a63-43f4-9fa0-27b94973e7d0
-- title:
--   Lemma C.6 — $\beta$-Projected-Nadler reduces to $\beta$-Hölder-LocalOpt
-- statement:
--   For every fixed dimension $n\ge1$ and every fixed rational $\beta\in(0,1]$, there is a polynomial-time many-one reduction from $\beta$-Projected-Nadler on $[0,1]^n$ to $\beta$-Hölder-LocalOpt on $[0,1]^n$:
--   $$ \beta\text{-Projected-Nadler}\ \le_p\ \beta\text{-Hölder-LocalOpt}. $$
--   The source problem has only the numerical promise $0<\varepsilon_2<\varepsilon_1(1-k)$; the metric and completeness promise is not needed (Remark C.7). A reduction consists of a polynomial-time instance map and a polynomial-time decoder that maps every answer of the target instance to an answer of the source instance.
--
--   This is the CLS-membership half of Theorem 3.2, combined with Theorem C.4.
--
--   Differences from the source:
--   - generalization: the problems printed on $[0,1]^3$ (Definitions 1, 2, 5) → every fixed dimension $n \ge 1$, the problems on $[0,1]^n$; reason: Appendix C proves the reductions on $[0,1]^n$ (p.34: "for generality"; p.37: "works for any polynomial dimension n"); $n = 3$ is the printed case
--   - generalization: $\beta$-Projected-Nadler with the promises of Definition 1 → instances in the input format only, without the metric and completeness promise; reason: Remark C.7: the membership reduction holds for arbitrary well-behaved circuits; instances with the promise are a subset with the same answers
--   - encoding: circuits with the ranges $f:[0,1]^n\to[0,1]^n$, $p:[0,1]^n\to[0,1]$ (and $P(X)\subseteq X$, $d \in [0,D]$) → raw circuit outputs clipped to these ranges with $\min/\max$; reason: Remark C.7's coordinate-wise clipping; it leaves every in-range instance unchanged
--   - encoding: answers are points of the cube, parameters rational in binary → answers are tagged rational points (`encNat` tag followed by `encVector`s); reductions are the public `CardinalMatching.SearchReduces` (polynomial-time on Cook's Turing machines, every target answer decoded); reason: p.7's computational model: rational data in binary, polynomial-time many-one reductions with a decoder for every valid solution
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Lemma C.6, p.37, and Remark C.7, p.38

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NadlerCLS_pnSearch
import Definitions.Def_NadlerCLS_holderSearch

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- **Lemma C.6: β-Projected-Nadler reduces to β-Hölder-LocalOpt** (Xiong–Vlatakis-Gkaragkounis, *On the Complexity of Finding Fixed Points for Set-Valued
Contractions*, arXiv:2609.14101, held version of 2026-11-03, sha256 1fcc5a02…6dc485,
Lemma C.6, p.37: "For every fixed rational β ∈ (0, 1], β-PROJECTED-NADLER admits a
polynomial-time reduction to β-HÖLDER-LOCALOPT"). For every dimension `n ≥ 1` and every rational
`β ∈ (0, 1]`, β-Projected-Nadler (input format only, no metric promise) reduces to
β-Hölder-LocalOpt by a polynomial-time search reduction.

**Formalization Note** The source problem carries no metric promise (Remark C.7, p.38); the paper
prints the problems on `[0, 1]³` and runs the reduction on `[0, 1]ⁿ` (p.37). -/
theorem lemma_C_6 (n : ℕ) (hn : 1 ≤ n) (β : ℚ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    SearchReduces (pnSearch n β) (holderSearch n β) := by sorry

end NadlerCLS
