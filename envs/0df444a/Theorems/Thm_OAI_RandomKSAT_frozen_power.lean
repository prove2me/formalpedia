-- Prove2me | Theorems.Thm_OAI_RandomKSAT_frozen_power
-- name    : OAI.RandomKSAT.frozen_power
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T17:54:11.354691+00:00
-- url     : https://prove2.me/theorems/148a8213-7dca-4a53-8b32-0be328698bd4
-- title:
--   Kill ratios of consecutive widths: $\kappa_r^{(r+1)/r}/(r+1)\le\kappa_{r+1}$
-- statement:
--   For natural numbers $u,b,s$ let
--   $$
--   \kappa(u,b,s)=\frac{\binom bs}{2^s\binom us}
--   $$
--   be the *kill ratio*. Its meaning: consider assignments $a:[u]\to\{\mathrm T,\mathrm F\}$ of the variables $[u]=\{0,\dots,u-1\}$ and clauses of width $s$, i.e. an $s$-element set of variables with a sign for each, satisfied by an assignment that matches at least one of the signs. If $S$ is a nonempty set of assignments whose members all agree on exactly $b$ variables (the *frozen* variables of $S$), then $\kappa(u,b,s)$ is the probability that one uniformly random clause of width $s$ is violated by every member of $S$.
--
--   **Theorem.** Let $u,b,r$ be natural numbers with $r\ge1$, $b\le u$ and $r+1\le b$. Then
--   $$
--   \frac{\kappa(u,b,r)^{(r+1)/r}}{r+1}\le\kappa(u,b,r+1),
--   $$
--   where the left-hand side uses the real power with exponent $(r+1)/r$.
--
--   For a nonempty set $S$ of assignments with $b$ frozen variables, the theorem bounds the probability that a random clause of width $r+1$ kills $S$ from below by a power of the probability that a random clause of width $r$ kills $S$. This is the inequality that drives the comparison between a single random clause of width $r$ and a block of random clauses of width $r+1$.
--
--   **Formalization Note** `killRatio u b s` uses real division, the exponent is `((r : ℝ)+1)/r`, and the power is `Real.rpow`; since $\kappa\ge0$ it is the usual real power.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/FrozenReplacement.lean#L85-L102

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.frozen_power {u b r : ℕ} (hr : 1 ≤ r) (hbu : b ≤ u) (hrb : r+1 ≤ b) :
    (killRatio u b r) ^ (((r : ℝ)+1)/r) / (r+1) ≤ killRatio u b (r+1) := by sorry
