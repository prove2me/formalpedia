-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_covariance_quadratic
-- name    : OAI.MatchingEntropy.covariance_quadratic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:21:16.937002+00:00
-- url     : https://prove2.me/theorems/66074fd1-3259-41e9-8e5c-45e7256b74bc
-- title:
--   Quadratic form of a weighted second-moment matrix
-- statement:
--   Let $A$ and $I$ be finite index sets, let $(p_a)_{a\in A}$ be nonnegative real weights ($p_a\ge 0$; they need not sum to $1$), and let $(b_a)_{a\in A}$ be vectors in $\mathbb{R}^I$. Define the $I\times I$ matrix
--
--   $$
--   C=WW^{\top},\qquad W_{i,a}=\sqrt{p_a}\,b_a(i)\quad(i\in I,\ a\in A),
--   $$
--
--   so that $C=\sum_a p_a\,b_ab_a^{\top}$ is the weighted second-moment matrix of the family. Then for every $u\in\mathbb{R}^I$
--
--   $$
--   u^{\top}Cu=\sum_{a\in A}p_a\,\langle b_a,u\rangle^2 .
--   $$
--
--   When $p$ is a probability vector and the vectors $b_a$ are centred, $C$ is the covariance matrix of the random vector $b_a$ with $a\sim p$, and the identity says that the quadratic form of $C$ at $u$ is the variance of the scalar $\langle b_a,u\rangle$. In the matching-entropy argument it converts the second moment of a centred linear score on perfect matchings into the quadratic form of the normalized matching covariance.
--
--   **Formalization Note** $C$ is `covariance p b := weightedColumns p b * (weightedColumns p b)ᵀ`; the hypothesis $p\ge 0$ is what gives $(\sqrt{p_a})^2=p_a$. The left-hand side is written `u ⬝ᵥ (covariance p b *ᵥ u)` and $\langle b_a,u\rangle$ is `b a ⬝ᵥ u`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Covariance.lean#L57-L72

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Polytope
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Face
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Covariance

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
open Matrix
variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]

omit [DecidableEq A] [DecidableEq I] in
theorem OAI.MatchingEntropy.covariance_quadratic {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ)
    (u : I → ℝ) : u ⬝ᵥ (covariance p b *ᵥ u) = ∑ a, p a*(b a ⬝ᵥ u)^2 := by sorry
