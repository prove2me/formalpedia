-- Prove2me | Theorems.Thm_NadlerCLS_lemma_C_8
-- name    : NadlerCLS.lemma_C_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:06:41.236792+00:00
-- url     : https://prove2.me/theorems/9a9ce651-cee9-4bba-80f5-f22a2c83f44a
-- title:
--   Lemma C.8 — Continuous-LocalOpt reduces to $\beta$-Projected-Nadler with every promise
-- statement:
--   For every fixed dimension $n\ge1$ and every fixed rational $\beta\in(0,1]$ there is a polynomial-time many-one reduction from Continuous-LocalOpt on $[0,1]^n$ to $\beta$-Projected-Nadler on $[0,1]^n$ whose target instances satisfy **every** promise of Definition 1, including that $([0,1]^n,d)$ is a complete metric space:
--   $$ \text{Continuous-LocalOpt}\ \le_p\ \beta\text{-Projected-Nadler (promise version)}. $$
--   In the paper the target is $d=d_p$, $\Pi(x,z)=f(x)$, $D=2$, $k=1-\delta/2$, $\varepsilon_1=1/2$, $\varepsilon_2=\delta/8$, $L_P=n\lambda$, $L_d=\lambda$ (C.8)–(C.9).
--
--   Differences from the source:
--   - generalization: the problems printed on $[0,1]^3$ (Definitions 1, 2, 5) → every fixed dimension $n \ge 1$, the problems on $[0,1]^n$; reason: Appendix C proves the reductions on $[0,1]^n$ (p.34: "for generality"; p.37: "works for any polynomial dimension n"); $n = 3$ is the printed case
--   - reading: a reduction to $\beta$-Projected-Nadler, a promise problem → a reduction to `pnPromiseSearch`: the target instances satisfy the metric and completeness promise; reason: Remark 3.1: "the instances built in our hardness reduction satisfy every promise"; it also gives the reduction to the problem without the promise
--   - encoding: circuits with the ranges $f:[0,1]^n\to[0,1]^n$, $p:[0,1]^n\to[0,1]$ (and $P(X)\subseteq X$, $d \in [0,D]$) → raw circuit outputs clipped to these ranges with $\min/\max$; reason: Remark C.7's coordinate-wise clipping; it leaves every in-range instance unchanged
--   - encoding: answers are points of the cube, parameters rational in binary → answers are tagged rational points (`encNat` tag followed by `encVector`s); reductions are the public `CardinalMatching.SearchReduces` (polynomial-time on Cook's Turing machines, every target answer decoded); reason: p.7's computational model: rational data in binary, polynomial-time many-one reductions with a decoder for every valid solution
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Lemma C.8, p.38, and Remark 3.1, p.9

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NadlerCLS_coSearch
import Definitions.Def_NadlerCLS_pnPromiseSearch

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- **Lemma C.8: Continuous-LocalOpt reduces to promised β-Projected-Nadler** (Xiong–Vlatakis-Gkaragkounis, *On the Complexity of Finding Fixed Points for Set-Valued
Contractions*, arXiv:2609.14101, held version of 2026-11-03, sha256 1fcc5a02…6dc485,
Lemma C.8, p.38: "For every fixed rational β ∈ (0, 1], CONTINUOUS-LOCALOPT admits a
polynomial-time reduction to β-PROJECTED-NADLER"). For every `n ≥ 1` and rational `β ∈ (0, 1]`,
Continuous-LocalOpt on `[0, 1]ⁿ` reduces by a polynomial-time search reduction to
β-Projected-Nadler restricted to instances satisfying **every** promise of Definition 1, the metric
and completeness promise included (Remark 3.1: "the instances built in our hardness reduction
satisfy every promise").

**Formalization Note** The target is `pnPromiseSearch`; since its answers are those of
`pnSearch`, this also gives the reduction to `pnSearch`. -/
theorem lemma_C_8 (n : ℕ) (hn : 1 ≤ n) (β : ℚ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    SearchReduces (coSearch n) (pnPromiseSearch n β) := by sorry

end NadlerCLS
