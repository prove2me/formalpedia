-- Prove2me | Theorems.Thm_NadlerCLS_theorem_3_2
-- name    : NadlerCLS.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:06:20.275363+00:00
-- url     : https://prove2.me/theorems/96329dd5-4c3a-4818-9395-d7a8c1e8ddeb
-- title:
--   Theorem 3.2 — $\beta$-Projected-Nadler is CLS-complete for every fixed rational $\beta\in(0,1]$
-- statement:
--   For every fixed rational $\beta\in(0,1]$, the problem $\beta$-Projected-Nadler on $X=[0,1]^3$ is CLS-complete:
--
--   1. **membership**: for some $k$, $\beta$-Projected-Nadler with only the numerical promise $0<\varepsilon_2<\varepsilon_1(1-k)$ and with answers bounded in length by $(|s|+1)^k+k$ is in CLS, and it is CLS-hard;
--   2. **hardness**: $\beta$-Projected-Nadler restricted to instances that satisfy every promise of Definition 1 (in particular, $(X,d)$ is a complete metric space) is CLS-hard: every problem in CLS reduces to it.
--
--   Here CLS is the class of total search problems with polynomially bounded, polynomial-time checkable answers that reduce to Continuous-LocalOpt. The theorem places the computational version of Nadler's fixed-point theorem for set-valued contractions exactly at the level of continuous local search.
--
--   Differences from the source:
--   - reading: $X=[0,1]^n$ ("this choice is inessential", p.9) → $X=[0,1]^3$; reason: Definition 2 and the platform's canonical `clsSearch` are three-dimensional; with $n$ in the input, membership would need the cited dimension reduction [DP11], which the paper does not prove
--   - reading: CLS-completeness of a problem with promises (Remarks 3.1, C.7) → membership for the problem with only the numerical promise, hardness for the problem with every promise; reason: Remark C.7: membership and totality hold for arbitrary well-behaved circuits; Remark 3.1: the hardness instances satisfy every promise; this is the strongest reading
--   - reading: CLS-complete → membership of the length-bounded problem `bounded (pnSearch 3 β) k` for some $k$, the house form of the platform; reason: CLS ⊆ TFNP requires polynomially bounded answers while the problem's rational answers are unbounded; hardness is stated for the unbounded promise problem, which is stronger
--   - encoding: CLS, CLS-hard, CLS-complete → the public `NetworkEquilibriumCLS.LinearNash` notions over its canonical `clsSearch` (max norm, one circuit); reason: the platform's class; equal to the paper's by the $\ell_1$/$\ell_\infty$ milestone
--   - encoding: circuits with the ranges $f:[0,1]^n\to[0,1]^n$, $p:[0,1]^n\to[0,1]$ (and $P(X)\subseteq X$, $d \in [0,D]$) → raw circuit outputs clipped to these ranges with $\min/\max$; reason: Remark C.7's coordinate-wise clipping; it leaves every in-range instance unchanged
--   - encoding: answers are points of the cube, parameters rational in binary → answers are tagged rational points (`encNat` tag followed by `encVector`s); reductions are the public `CardinalMatching.SearchReduces` (polynomial-time on Cook's Turing machines, every target answer decoded); reason: p.7's computational model: rational data in binary, polynomial-time many-one reductions with a decoder for every valid solution
--   - encoding: fixed rational $\beta$, $\|\cdot\|_1^{\beta}$ → $\beta$ a parameter of the problem; `Real.rpow` of an explicit $\ell_1$ sum; reason: p.31: "The exponent β is not part of the input"; Mathlib's norm is the sup norm
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Theorem 3.2, p.11; proof: "the proof of Theorem 3.2 naturally follows from Lemma C.8 and C.6", p.39

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_NadlerCLS_pnSearch
import Definitions.Def_NadlerCLS_pnPromiseSearch

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- **Theorem 3.2: β-Projected-Nadler is CLS-complete** (Xiong–Vlatakis-Gkaragkounis, *On the
Complexity of Finding Fixed Points for Set-Valued Contractions*, arXiv:2609.14101, held version of
2026-11-03, sha256 1fcc5a02…6dc485, Theorem 3.2, p.11: "The problem β-PROJECTED-NADLER is
CLS-complete for any fixed rational β ∈ (0, 1]"). For every rational `β ∈ (0, 1]`, on
`X = [0, 1]³`:

1. **membership**: β-Projected-Nadler with only the numerical promise (`pnSearch`), its answers
   bounded by a fixed polynomial `(|s| + 1)^k + k` of the instance length for some `k`, is in CLS
   and CLS-hard, i.e. CLS-complete;
2. **hardness**: β-Projected-Nadler restricted to instances that also satisfy the metric and
   completeness promise (`pnPromiseSearch`) is CLS-hard.

**Formalization Note** CLS, TFNP, CLS-hard and CLS-complete are the public
`NetworkEquilibriumCLS.LinearNash` notions over its canonical three-dimensional `clsSearch`. The
dimension is `n = 3` (Definition 2's dimension; p.9: "this choice is inessential"). `β` is a fixed
rational, not part of the input. The decidable numerical promise is in the input format; the
metric and completeness promise is only in `pnPromiseSearch` (Remarks 3.1 and C.7). Ranges are
enforced by clipping; answers are tagged rational points; the norm is ℓ₁. -/
theorem theorem_3_2 (β : ℚ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (∃ k : ℕ, CLSComplete (bounded (pnSearch 3 β) k)) ∧ CLSHard (pnPromiseSearch 3 β) := by sorry

end NadlerCLS
