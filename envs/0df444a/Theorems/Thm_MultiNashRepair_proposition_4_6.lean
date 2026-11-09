-- Prove2me | Theorems.Thm_MultiNashRepair_proposition_4_6
-- name    : MultiNashRepair.proposition_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:36:16.669815+00:00
-- url     : https://prove2.me/theorems/ad6f776f-c48b-4ac5-a056-8c4df32ba749
-- title:
--   Proposition 4.6 — a $\sigma$-dependent iteration bound and running time $B^{O_\sigma(1)}$
-- statement:
--   Fix a rational target $\sigma\in(1,\sigma_\star)$ and admissible controls for it.
--   1. The number of iterations of Algorithm 1 is bounded by a constant depending only on $\sigma$: there is $N_0$ such that, for every $m\ge m_0$ and every game with payoffs in $[0,1]$, every state reachable at iteration $k$ has $k\le N_0$ (the paper gives $N_0=1+\lceil(\sigma-1)/\Delta_0\rceil+\lceil R_\Phi/\kappa\rceil+1$, (5.63)).
--   2. Its running time on explicitly listed rational payoff tensors is $B^{O_\sigma(1)}$: there are one machine and one constant $c$ such that, on every complete rational table with $m\ge1$ players and input length $B$, the machine outputs within $c(B+2)^c$ steps the encoding of an output of Algorithm 1 (the initial profile when $m<m_0$, the profile of a terminal reachable state otherwise).
--
--   Differences from the source:
--   - reading: the number of iterations is bounded by a constant depending only on $\sigma$ → $\exists N_0$ after the controls (which depend only on $\sigma$), bounding the iteration index of every reachable state, for every $m\ge m_0$ and every game; reason: the controls are fixed from $\sigma$ before the game is read
--   - reading: running time $B^{O_\sigma(1)}$ → one multi-stack Turing machine and one $c$ with time $c(B+2)^c$ whose output is an output of Algorithm 1; reason: the paper names no machine model; the output clause makes the machine implement Algorithm 1 with some admissible choices
--   - generalization: rational games → the iteration bound (1) for every real game with payoffs in $[0,1]$; reason: contains the rational case
--   - encoding: $m$-player games → $m\ge1$ in (2); reason: a game has at least one player; an initial profile with $\varsigma\ge1$ needs $m\ge1$
--   - encoding: players $[m]$, nonempty action sets $A_i$, payoffs in $[0,1]\cap\mathbb Q$, the binary input → the published `Table m` (players `Fin m`, actions `Fin (n i)`, payoffs $p/q$ with $p\le q$, possibly unreduced) and its encoding `encGame`; reason: Lean representation of the paper's input; the same instances
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), Proposition 4.6, p.14; proof §5.6, (5.62)–(5.63), pp.43–45

import Mathlib
import Definitions.Def_NashAmplification_Filtering_Encoding
import Definitions.Def_CFLOutliers_OutputsWithin
import Definitions.Def_MultiNashRepair_IDRH

open OnlineCRS.Combine (Sym)
open NashAmplification.Filtering (Utility BoundedGame Table RawProfile encGame encProfile)

namespace MultiNashRepair

/-- **Proposition 4.6 (Bounded Iterations and Bit Complexity)** (Tang, Ding, Fang,
arXiv:2611.06076, Proposition 4.6, p.14; proof §5.6, pp.43–45).

For each fixed rational target `σ ∈ (1, σ⋆)` and admissible controls for it:
(i) the number of iterations of Algorithm 1 is bounded by a constant depending only on `σ`: one
`N0` bounds the iteration index of every reachable state, for every `m ≥ m0` and every game with
payoffs in `[0,1]` (the paper gives `N0 = 1 + ⌈(σ − 1)/Δ0⌉ + ⌈R_Φ/κ⌉ + 1`, (5.63));
(ii) its running time on explicitly listed rational payoff tensors is `B^{O_σ(1)}`: one machine
and one exponent `c` such that, on every complete rational table with `m ≥ 1` players, the
machine outputs within `c (B + 2)^c` steps the encoding of an output of Algorithm 1 (the initial
profile when `m < m0`, the profile of a terminal reachable state otherwise).

**Formalization Note.** The controls depend only on `σ`, so "a constant depending only on `σ`"
is `∃ N0` after the controls. (ii) implements Algorithm 1 with some admissible choices, including
halting with an admissible output on every rational game. `m ≥ 1`: a game has at least one
player. -/
theorem proposition_4_6 (σ : ℚ) (hσ1 : 1 < σ) (hσ2 : (σ : ℝ) < sigmaStar)
    (ctrl : Controls σ) :
    (∃ N0 : ℕ, ∀ (m : ℕ) (n : Fin m → ℕ) (u : Utility n), ctrl.m0 ≤ m → (∀ i, 0 < n i) →
      BoundedGame u → ∀ (k : ℕ) (s : State n), Reach ctrl u k s → k ≤ N0) ∧
    (∃ (M : Turing.TM2ComputableAux Sym Sym) (c : ℕ), ∀ m : ℕ, 1 ≤ m → ∀ G : Table m,
      ∃ x : RawProfile m, x.sizes = G.sizes ∧
        CFLOutliers.OutputsWithin M (encGame G) (encProfile x) (c * ((encGame G).length + 2) ^ c) ∧
        IDRHOutput ctrl G.utility (x.on G.counts)) := by sorry

end MultiNashRepair
