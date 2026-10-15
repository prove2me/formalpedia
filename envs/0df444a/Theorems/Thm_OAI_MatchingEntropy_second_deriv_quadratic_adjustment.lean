-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_second_deriv_quadratic_adjustment
-- name    : OAI.MatchingEntropy.second_deriv_quadratic_adjustment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:03:35.616012+00:00
-- url     : https://prove2.me/theorems/f016c98a-3b52-46a6-a710-2800ff7f3050
-- title:
--   Second derivative at $0$ of $f(t)+c_0+c_1t+vt^2-g(t)$ from first-derivative data
-- statement:
--   Let $f,g,f_1,g_1:\mathbb R\to\mathbb R$ be functions such that, for all $t$ in some neighbourhood of $0$, $f$ is differentiable at $t$ with $f'(t)=f_1(t)$ and $g$ is differentiable at $t$ with $g'(t)=g_1(t)$. Suppose moreover that $f_1$ and $g_1$ are differentiable at $0$, with $f_1'(0)=\alpha$ and $g_1'(0)=\beta$. Let $c_0,c_1,v\in\mathbb R$ and
--
--   $$
--   \varphi(t)=f(t)+c_0+c_1t+vt^2-g(t).
--   $$
--
--   Then the derivative function $\varphi'$ is differentiable at $0$ and
--
--   $$
--   (\varphi')'(0)=\alpha+2v-\beta .
--   $$
--
--   This is a bookkeeping lemma for the second-variation argument: there $f$ is the entropy barrier composed with the entropy along a line, $g$ is a log-partition function, and the quadratic polynomial collects the terms produced by the exponential-tilt bound. It reduces the second derivative of the comparison function to the second derivatives of $f$ and $g$ separately.
--
--   **Formalization Note** $\varphi'$ is Mathlib's `deriv`, which is defined everywhere (and equals $0$ at points of non-differentiability); the conclusion is `HasDerivAt (deriv φ) (α + 2v - β) 0`. The neighbourhood hypotheses are stated with the filter `𝓝 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Calculus.lean#L149-L168

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter

theorem OAI.MatchingEntropy.second_deriv_quadratic_adjustment {f fD g gD : ℝ → ℝ} {fDD gDD c₀ c₁ v : ℝ}
    (hf : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt f (fD t) t)
    (hg : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt g (gD t) t)
    (hfD : HasDerivAt fD fDD 0) (hgD : HasDerivAt gD gDD 0) :
    HasDerivAt (deriv (fun t => f t+c₀+t*c₁+t^2*v-g t))
      (fDD+2*v-gDD) 0 := by sorry
