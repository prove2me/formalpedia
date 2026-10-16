-- Prove2me | Theorems.Thm_OAI_RandomKSAT_killRatio_le_density_pow
-- name    : OAI.RandomKSAT.killRatio_le_density_pow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T17:53:49.233629+00:00
-- url     : https://prove2.me/theorems/79624c67-d28f-4755-b55f-ad09606d7f41
-- title:
--   Kill ratio bound $\binom bs/(2^s\binom us)\le(b/2u)^s$
-- statement:
--   For natural numbers $u,b,s$ let
--   $$
--   \kappa(u,b,s)=\frac{\binom bs}{2^s\binom us}
--   $$
--   be the *kill ratio*. Its meaning: consider assignments $a:[u]\to\{\mathrm T,\mathrm F\}$ of the variables $[u]=\{0,\dots,u-1\}$ and clauses of width $s$, i.e. an $s$-element set of variables with a sign for each, satisfied by an assignment that matches at least one of the signs. If $S$ is a nonempty set of assignments whose members all agree on exactly $b$ variables (the *frozen* variables of $S$), then $\kappa(u,b,s)$ is the probability that one uniformly random clause of width $s$ is violated by every member of $S$.
--
--   **Theorem.** If $b\le u$ and $s\le u$, then
--   $$
--   \frac{\binom bs}{2^s\binom us}\le\Big(\frac{b}{2u}\Big)^s .
--   $$
--
--   The right-hand side is the probability that $s$ independently and uniformly chosen variables are all frozen and all receive the sign opposing the common value, so the bound says that choosing the clause variables without repetition can only lower this probability. It yields $\kappa(u,b,s)\le2^{-s}$ and the root bound $\kappa(u,b,s)^{1/s}\le b/(2u)$, which feed the comparison of kill probabilities of clauses of consecutive widths.
--
--   **Formalization Note** `killRatio u b s` uses real division. When $u=0$ the hypotheses force $b=s=0$, and both sides equal $1$ (with Lean's conventions $b/(2u)=0$ and $0^0=1$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/FrozenReplacement.lean#L40-L59

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.killRatio_le_density_pow {u b s : ℕ} (hbu : b ≤ u) (hsu : s ≤ u) :
    killRatio u b s ≤ ((b : ℝ) / (2 * u)) ^ s := by sorry
