-- Prove2me | Theorems.Thm_OAI_TreeEdit_PrimeSupply_eventually_pi_power
-- name    : OAI.TreeEdit.PrimeSupply.eventually_pi_power
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:12:31.695868+00:00
-- url     : https://prove2.me/theorems/26e821c0-0520-4415-922c-08a4c7c284fe
-- title:
--   For each $a \ge 1$, eventually $\pi(k^{a+1}) \ge 2k^a$
-- statement:
--   For a natural number $n$ let $\pi(n)$ denote the number of primes $p$ with $p \le n$.
--
--   **Theorem.** For every integer $a \ge 1$ there is $k_0$ such that for all integers $k \ge k_0$
--
--   $$
--   2k^a \le \pi\big(k^{a+1}\big).
--   $$
--
--   Since $\pi(k^a) \le k^a$, it follows that the interval $(k^a, k^{a+1}]$ contains at least $k^a$ primes for all large $k$. With $a = 2$ this supplies the pool of primes between $k^2$ and $k^3$ from which the random tree configurations in the edit-distance lower bound are built.
--
--   **Formalization Note** The statement is phrased with the filter `atTop` on the natural numbers, and $\pi$ is Mathlib's `Nat.primeCounting`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/PrimeSupply.lean#L21-L65

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_SampledSpectrum
import Definitions.Def_OAI_Combinatorics_TreeEdit_PrimeSupply

open OAI OAI.TreeEdit OAI.TreeEdit.PrimeSupply
universe u
attribute [local instance] Classical.propDecidable
open Filter

theorem OAI.TreeEdit.PrimeSupply.eventually_pi_power (a : ℕ) (ha : 1 ≤ a) :
    ∀ᶠ k : ℕ in atTop, 2 * k ^ a ≤ (k ^ (a + 1)).primeCounting := by sorry
