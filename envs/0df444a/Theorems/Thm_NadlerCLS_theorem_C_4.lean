-- Prove2me | Theorems.Thm_NadlerCLS_theorem_C_4
-- name    : NadlerCLS.theorem_C_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:02:39.537987+00:00
-- url     : https://prove2.me/theorems/4a686b96-b013-43c0-9b97-e0c77820b43b
-- title:
--   Theorem C.4 — $\beta$-Hölder-LocalOpt is CLS-complete
-- statement:
--   For every fixed rational $\beta\in(0,1]$, $\beta$-Hölder-LocalOpt on $[0,1]^3$ is CLS-complete:
--
--   1. **membership and hardness**: for some $k$, the problem whose answers are additionally bounded in length by $(|s|+1)^k+k$ for an instance $s$ is in CLS (a TFNP problem reducing to Continuous-LocalOpt) and CLS-hard;
--   2. **hardness**: the problem itself (answers of any length) is CLS-hard: every problem in CLS reduces to it.
--
--   Differences from the source:
--   - reading: CLS-complete → $(\exists k,\ \text{CLS-complete}(\text{bounded}_k(\beta\text{-Hölder-LocalOpt})))\wedge\text{CLS-hard}(\beta\text{-Hölder-LocalOpt})$; reason: CLS ⊆ TFNP requires polynomially bounded answers while the problem's rational answers are unbounded; hardness for the unbounded problem is the stronger hardness
--   - encoding: CLS, CLS-hard and CLS-complete → the public `NetworkEquilibriumCLS.LinearNash` `InCLS`, `CLSHard`, `CLSComplete` over the canonical `clsSearch`; reason: the platform's class; equal to the paper's by the $\ell_1$/$\ell_\infty$ milestone
--   - encoding: circuits with the ranges $f:[0,1]^n\to[0,1]^n$, $p:[0,1]^n\to[0,1]$ (and $P(X)\subseteq X$, $d \in [0,D]$) → raw circuit outputs clipped to these ranges with $\min/\max$; reason: Remark C.7's coordinate-wise clipping; it leaves every in-range instance unchanged
--   - encoding: answers are points of the cube, parameters rational in binary → answers are tagged rational points (`encNat` tag followed by `encVector`s); reductions are the public `CardinalMatching.SearchReduces` (polynomial-time on Cook's Turing machines, every target answer decoded); reason: p.7's computational model: rational data in binary, polynomial-time many-one reductions with a decoder for every valid solution
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Theorem C.4, p.37

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_NadlerCLS_holderSearch

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- **Theorem C.4: β-Hölder-LocalOpt is CLS-complete** (Xiong–Vlatakis-Gkaragkounis, *On the
Complexity of Finding Fixed Points for Set-Valued Contractions*, arXiv:2609.14101, held version of
2026-11-03, sha256 1fcc5a02…6dc485, Theorem C.4, p.37: "For every fixed rational β ∈ (0, 1], the
problem β-HÖLDER-LOCALOPT is CLS-complete"). For every rational `β ∈ (0, 1]`, β-Hölder-LocalOpt on
`[0, 1]³` (Definition 5)

1. is CLS-complete once its answers are bounded by a fixed polynomial `(|s| + 1)^k + k` of the
   instance length, for some `k`; and
2. is CLS-hard.

**Formalization Note** CLS, TFNP, CLS-hard and CLS-complete are the public
`NetworkEquilibriumCLS.LinearNash` notions over its canonical `clsSearch`; membership in TFNP
requires polynomially bounded answers, which is why membership is stated for the public
`bounded` restriction. -/
theorem theorem_C_4 (β : ℚ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (∃ k : ℕ, CLSComplete (bounded (holderSearch 3 β) k)) ∧ CLSHard (holderSearch 3 β) := by sorry

end NadlerCLS
