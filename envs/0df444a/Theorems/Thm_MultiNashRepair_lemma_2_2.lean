-- Prove2me | Theorems.Thm_MultiNashRepair_lemma_2_2
-- name    : MultiNashRepair.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:28:19.442196+00:00
-- url     : https://prove2.me/theorems/80b0e17e-d99e-45ae-b778-c3eeacb8f095
-- title:
--   Lemma 2.2 — rational initialization: $\mathrm{Reg}(x^{(0)})\le1-1/m$ in polynomial time, uniformly in $m$
-- statement:
--   For every rational $m$-player game with payoffs in $[0,1]$, a rational product profile $x^{(0)}$ with
--   $$\sigma^{(0)}=m\bigl(1-\mathrm{Reg}(x^{(0)})\bigr)\ge1,\qquad\text{i.e.}\qquad \mathrm{Reg}(x^{(0)})\le1-\frac1m,$$
--   can be computed in polynomial time: one machine and one constant $c$ serve every $m\ge1$, with time at most $c(N+2)^c$ on an input of length $N$.
--
--   This is the starting profile of Algorithm 1.
--
--   Differences from the source:
--   - reading: computed in polynomial time (no machine model named) → one multi-stack Turing machine and one exponent $c$ with time at most $c(N+2)^c$ on inputs of length $N$ (the published `CFLOutliers.OutputsWithin`), outputting the encoding of the profile; reason: the paper names no model; polynomial time is invariant under polynomial simulations
--   - encoding: $\sigma^{(0)}\ge1$ → `IsEpsApproxNash` with $\varepsilon=1-1/m$; reason: $\sigma^{(0)}=m(1-\mathrm{Reg})$; equivalent by multilinearity
--   - encoding: $m$-player games → $m\ge1$; reason: $\sigma^{(0)}\ge1$ is impossible for $m=0$; the paper's games have players $[m]\ne\emptyset$
--   - encoding: players $[m]$, nonempty action sets $A_i$, payoffs in $[0,1]\cap\mathbb Q$, the binary input → the published `Table m` (players `Fin m`, actions `Fin (n i)`, payoffs $p/q$ with $p\le q$, possibly unreduced) and its encoding `encGame`; reason: Lean representation of the paper's input; the same instances
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), Lemma 2.2, p.5

import Mathlib
import Definitions.Def_DGPNash_WellSupported_Equilibria
import Definitions.Def_NashAmplification_Filtering_Encoding
import Definitions.Def_CFLOutliers_OutputsWithin

open OnlineCRS.Combine (Sym)
open NashAmplification.Filtering (Table RawProfile encGame encProfile)

namespace MultiNashRepair

/-- **Lemma 2.2 (Rational Initialization)** (Tang, Ding, Fang, arXiv:2611.06076, Lemma 2.2,
p.5).

For every rational `m`-player game with payoffs in `[0,1]`, a rational product profile `x^{(0)}`
with `σ^{(0)} = m (1 − Reg(x^{(0)})) ≥ 1`, i.e. `Reg(x^{(0)}) ≤ 1 − 1/m`, can be computed in
polynomial time.

**Formalization Note.** One `TM2` machine and one exponent serve every `m ≥ 1` (Algorithm 1
line 2 runs the construction for every player count). `σ^{(0)} ≥ 1` is impossible for `m = 0`,
so `1 ≤ m`. `IsEpsApproxNash` with `ε = 1 − 1/m` is `Reg ≤ 1 − 1/m` by multilinearity. -/
theorem lemma_2_2 :
    ∃ (M : Turing.TM2ComputableAux Sym Sym) (c : ℕ),
      ∀ m : ℕ, 1 ≤ m → ∀ G : Table m,
        ∃ x : RawProfile m, x.sizes = G.sizes ∧
          CFLOutliers.OutputsWithin M (encGame G) (encProfile x) (c * ((encGame G).length + 2) ^ c) ∧
          DGPNash.WellSupported.IsEpsApproxNash G.utility (x.on G.counts)
            (1 - 1 / (m : ℝ)) := by sorry

end MultiNashRepair
