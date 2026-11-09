-- Prove2me | Theorems.Thm_MultiNashRepair_lemma_2_1
-- name    : MultiNashRepair.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:29:53.09186+00:00
-- url     : https://prove2.me/theorems/955327b6-f1c8-4a29-9636-0b029acd8d0c
-- title:
--   Lemma 2.1 — one-player extension: an $\alpha$-ANE algorithm for $r$ players gives a $1/(2-\alpha)$-ANE algorithm for $r+1$ players
-- statement:
--   Let $r\in\mathbb N$ and $\alpha\in\mathbb Q\cap[0,1]$. Suppose that a rational $\alpha$-approximate Nash equilibrium can be computed in polynomial time for $r$-player games with rational payoffs in $[0,1]$. Then a rational
--   $$\frac{1}{2-\alpha}\text{-approximate Nash equilibrium}$$
--   can be computed in polynomial time for $(r+1)$-player games.
--
--   Iterating it from one player gives the classical $1-1/m$ guarantee, and Proposition 2.3 of the paper shows that iteration cannot improve the leading coefficient of $1/m$.
--
--   Differences from the source:
--   - reading: computed in polynomial time (no machine model named) → one multi-stack Turing machine and one exponent $c$ with time at most $c(N+2)^c$ on inputs of length $N$ (the published `CFLOutliers.OutputsWithin`), outputting the encoding of the profile; reason: the paper names no model; polynomial time is invariant under polynomial simulations
--   - generalization: $r$-player games (for $r\ge1$ implicitly) → every $r\in\mathbb N$, including $r=0$; reason: the $r=0$ case is true (one player: a pure best response is exact) and the statement specializes to every $r\ge1$
--   - encoding: $x$ is an $\varepsilon$-approximate Nash equilibrium, $\mathrm{Reg}(x)\le\varepsilon$ (pure deviations) → `IsEpsApproxNash` (every mixed unilateral deviation gains at most $\varepsilon$); reason: by multilinearity the best mixed deviation gains at most the best pure deviation; equivalent
--   - encoding: players $[m]$, nonempty action sets $A_i$, payoffs in $[0,1]\cap\mathbb Q$, the binary input → the published `Table m` (players `Fin m`, actions `Fin (n i)`, payoffs $p/q$ with $p\le q$, possibly unreduced) and its encoding `encGame`; reason: Lean representation of the paper's input; the same instances
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), Lemma 2.1, p.5

import Mathlib
import Definitions.Def_MultiNashRepair_PolyANE

namespace MultiNashRepair

/-- **Lemma 2.1 (One-Player Extension [HdRS08])** (Tang, Ding, Fang, arXiv:2611.06076,
Lemma 2.1, p.5).

If a rational `α`-approximate Nash equilibrium (`α ∈ ℚ ∩ [0, 1]`) can be computed in polynomial
time for `r`-player games, then a rational `1/(2 − α)`-approximate Nash equilibrium can be
computed in polynomial time for `(r + 1)`-player games.

**Formalization Note.** "Can be computed in polynomial time for `k`-player games" is
`PolyANE k ε`: one `TM2` machine and one exponent for all complete rational `k`-player tables.
The statement holds for every `r : ℕ`, including `r = 0`. -/
theorem lemma_2_1 (r : ℕ) (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (h : PolyANE r α) :
    PolyANE (r + 1) (1 / (2 - (α : ℝ))) := by sorry

end MultiNashRepair
