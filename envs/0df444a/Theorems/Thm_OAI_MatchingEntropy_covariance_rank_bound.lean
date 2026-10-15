-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_covariance_rank_bound
-- name    : OAI.MatchingEntropy.covariance_rank_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:21:53.1951+00:00
-- url     : https://prove2.me/theorems/4ff82c90-aa15-480d-9370-88f9a2e31358
-- title:
--   Rank–trace bound for a positive semidefinite matrix satisfying a second-variation inequality
-- statement:
--   Let $\iota$ be a finite index set, let $C$ be a real $\iota\times\iota$ matrix that is positive semidefinite (symmetric, with $u^{\top}Cu\ge 0$ for all $u$), and let $a\in\mathbb{R}$. Suppose that for every $u\in\mathbb{R}^{\iota}$
--
--   $$
--   (a-1)\,\|Cu\|^2+u^{\top}Cu\le 0,
--   $$
--
--   where $\|Cu\|^2=\langle Cu,Cu\rangle$ is the squared Euclidean norm. Then
--
--   $$
--   \operatorname{rank}C\le(1-a)\operatorname{tr}C .
--   $$
--
--   The hypothesis is the shape of a second-order optimality condition. In the matching-entropy argument $C$ is the normalized matching covariance at a maximizer of the entropy defect and $a=8e^{-H(x)/m}$; combined with a lower bound on $\operatorname{rank}C$ and the exact value of $\operatorname{tr}C$, the inequality produces the final numerical contradiction. It applies to the full, possibly singular matrix $C$, without inverting $C$ on its image.
--
--   **Formalization Note** Positive semidefiniteness is Mathlib's `Matrix.PosSemidef`, the natural number `C.rank` is cast to $\mathbb{R}$, and $\|Cu\|^2$ is written `(C *ᵥ u) ⬝ᵥ (C *ᵥ u)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Covariance.lean#L154-L193

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

theorem OAI.MatchingEntropy.covariance_rank_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {a : ℝ}
    (hsecond : ∀ u : ι → ℝ,
      (a - 1) * ((C *ᵥ u) ⬝ᵥ (C *ᵥ u)) + u ⬝ᵥ (C *ᵥ u) ≤ 0) :
    (C.rank : ℝ) ≤ (1-a) * C.trace := by sorry
