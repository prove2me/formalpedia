-- Prove2me | Theorems.Thm_OAI_RandomKSAT_replacement_numeric
-- name    : OAI.RandomKSAT.replacement_numeric
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T17:54:35.967317+00:00
-- url     : https://prove2.me/theorems/7ddc851b-2002-4a81-801d-0f64c5245e3d
-- title:
--   Numerical core of replacing one random $r$-clause by $g$ random $(r+1)$-clauses
-- statement:
--   For natural numbers $u,b,s$ let $\kappa(u,b,s)=\binom bs/(2^s\binom us)$ be the kill ratio: if $S$ is a nonempty set of assignments of $u$ Boolean variables whose members all agree on exactly $b$ variables, it is the probability that a uniformly random clause of width $s$ on these variables (an $s$-element set of variables with a sign for each, satisfied by an assignment matching at least one sign) is violated by every member of $S$. For $r\ge1$ put $K_{r+1}=(2^{r+1}r)^r$.
--
--   **Theorem.** Let $u,b,r,g$ be natural numbers with $r\ge2$, $b\le u$, $r+1\le u$ and $g\ge1$, and let $R\ge0$ be a real number such that
--
--   1. $1-\exp\big(-g\,\kappa(u,b,r+1)\big)\le R$, and
--   2. if $2^{r+2}u\le g$, then $R\ge\tfrac13$.
--
--   Then
--   $$
--   \kappa(u,b,r)-\frac{K_{r+1}}{g^r}\le R .
--   $$
--
--   In the application, $R$ is the probability that $g$ independent random clauses of width $r+1$ kill a set $S$ of assignments with $b$ frozen variables: condition 1 accounts for the chance that one of the $g$ clauses kills $S$ on its own, and condition 2 for a union bound over all assignments when the block is very long. The theorem isolates the purely numerical part of the comparison: a single random clause of width $r$ kills $S$ with probability $\kappa(u,b,r)$, and up to the error $K_{r+1}/g^r$ this is at most $R$.
--
--   **Formalization Note** $K_{r+1}$ is `replacementK (r+1)`, where `replacementK k` $=(2^k(k-1))^{k-1}$ with natural-number subtraction; at $k=r+1$ it equals $(2^{r+1}r)^r$. Condition 2 is the hypothesis `(2 : ℝ)^(r+2)*u ≤ g → 1/3 ≤ R`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/BlockKilling.lean#L204-L275

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.replacement_numeric {u b r g : ℕ} (hr : 2 ≤ r) (hbu : b ≤ u)
    (hru : r+1 ≤ u) (hg : 1 ≤ g) {R : ℝ} (hR : 0 ≤ R)
    (hind : 1-Real.exp (-(g : ℝ)*killRatio u b (r+1)) ≤ R)
    (hlong : (2 : ℝ)^(r+2)*u ≤ g → (1 : ℝ)/3 ≤ R) :
    killRatio u b r - replacementK (r+1)/(g : ℝ)^r ≤ R := by sorry
