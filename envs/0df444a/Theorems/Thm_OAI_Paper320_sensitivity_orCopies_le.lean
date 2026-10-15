-- Prove2me | Theorems.Thm_OAI_Paper320_sensitivity_orCopies_le
-- name    : OAI.Paper320.sensitivity_orCopies_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:48:57.52777+00:00
-- url     : https://prove2.me/theorems/9f75ab92-3a51-4b5c-8786-4d98aa34cc99
-- title:
--   Sensitivity of an OR of disjoint copies is controlled by the 0- and 1-sensitivities
-- statement:
--   Let $I$ and $K$ be finite sets, identify Boolean values with $\{0,1\}$, and let $f : \{0,1\}^I \to \{0,1\}$. For $x$ and a coordinate $i$ write $x^{\{i\}}$ for $x$ with coordinate $i$ flipped; the sensitivity of a function $h$ at $x$ is $s(h,x) = |\{ i : h(x^{\{i\}}) \ne h(x) \}|$ and its sensitivity is $s(h) = \max_x s(h,x)$. The OR of $|K|$ disjoint copies of $f$ is the function on $\{0,1\}^{K \times I}$
--   $$
--   (\mathrm{OR}_K \circ f)(x) = \bigvee_{k \in K} f(x_{k,\cdot}), \qquad x_{k,\cdot} = (x_{(k,a)})_{a \in I}.
--   $$
--
--   Suppose $S_0, S_1 \in \mathbb{N}$ bound the sensitivity of $f$ separately on its 0-inputs and on its 1-inputs: $s(f,x) \le S_0$ for every $x$ with $f(x) = 0$, and $s(f,x) \le S_1$ for every $x$ with $f(x) = 1$. Then
--
--   $$
--   s(\mathrm{OR}_K \circ f) \le \max\big(|K| \, S_0,\ S_1\big).
--   $$
--
--   This is a balancing device: if the 0-sensitivity of $f$ is about $|K|$ times smaller than its 1-sensitivity, the OR of $|K|$ copies has essentially the same sensitivity as $f$ on 1-inputs, while (for $f$ vanishing at the zero input) its block sensitivity at the zero input is multiplied by $|K|$. In the separation of block sensitivity from sensitivity it is applied with $|K| = M$, $S_0 = 2(d+2)M^d$ and $S_1 = 2(d+2)M^{d+1}$.
--
--   **Formalization Note** The function is `orCopies (K := K) f`, defined as `compose orBits f` where `orBits y` is true exactly when some coordinate of `y` is true. If $K$ is empty the OR is constantly false and the bound holds trivially.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/Or.lean#L40-L71

import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower
import Definitions.Def_OAI_Combinatorics_Sensitivity_TowerProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_ProfileArithmetic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_OAI_Combinatorics_Sensitivity_Or

open OAI OAI.Paper320
open scoped Classical BigOperators
variable {I K : Type} [Fintype K]
variable [Fintype I]

theorem OAI.Paper320.sensitivity_orCopies_le (f : (I → Bool) → Bool) (S₀ S₁ : ℕ)
    (h₀ : ∀ x, f x = false → sensitivityAt f x ≤ S₀)
    (h₁ : ∀ x, f x = true → sensitivityAt f x ≤ S₁) :
    sensitivity (orCopies (K := K) f) ≤ max (Fintype.card K * S₀) S₁ := by sorry
