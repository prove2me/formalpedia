-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_matching_defect_second_variation
-- name    : OAI.MatchingEntropy.matching_defect_second_variation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:05:11.696245+00:00
-- url     : https://prove2.me/theorems/f8ed90ed-356c-4b28-bca6-9659ec8b1c99
-- title:
--   Second-variation inequality at a maximizer of the matching entropy defect
-- statement:
--   Let $G$ be a loopless multigraph with vertex set $V$ and finite edge set $E$ (parallel edges allowed), let $\mathcal M(G)$ be its finite set of perfect matchings (edge sets covering every vertex exactly once) and $\mathbf 1_M\in\mathbb R^E$ the indicator vector of $M$. For a law (probability vector) $p$ on $\mathcal M(G)$ let $\operatorname{mean}(p)=\sum_M p_M\mathbf 1_M$, let $\mathcal F(y)$ be the set of laws with mean $y$, and let $\mathcal P(G)=\operatorname{conv}\{\mathbf 1_M:M\in\mathcal M(G)\}$ be the perfect matching polytope. For a vector $z$ indexed by any finite set write $H(z)=-\sum_i z_i\log z_i$ (with $0\log 0=0$), and let $\Phi_G(y)=\sup\{H(p):p\in\mathcal F(y)\}$. For $m\neq0$ let $B_m(h)=h-8m(1-e^{-h/m})$ be the entropy barrier and
--
--   $$
--   \mathcal D_m(y)=B_m\big(H(y)\big)-\Phi_G(y)
--   $$
--
--   the *entropy defect* of $y\in\mathbb R^E$. For $u\in\mathbb R^E$ and $c\in\mathbb R$ let $a(M)=\sum_e u_e\mathbf 1_M(e)-c$ be the affine score of a matching.
--
--   Let $x\in\mathbb R^E$, let $p\in\mathcal F(x)$ with $H(p)=\Phi_G(x)$, let $m\neq0$, and assume that $x$ maximizes the defect on the polytope: $\mathcal D_m(y)\le\mathcal D_m(x)$ for every $y\in\mathcal P(G)$. Let $u,c$ be such that the score is centered under $p$, $\sum_M p_M a(M)=0$, and let $w\in\mathbb R^E$ be its covariance with the edge indicators, $w_e=\sum_M p_M\,a(M)\,\mathbf 1_M(e)$. Then
--
--   $$
--   \big(8e^{-H(x)/m}-1\big)\sum_{e\in E}\frac{w_e^2}{x_e}\;+\;\frac{8e^{-H(x)/m}}{m}\Big(-\sum_{e}w_e\log x_e-\sum_e w_e\Big)^2\;+\;\sum_{M}p_M\,a(M)^2\;\le\;0 .
--   $$
--
--   The matching entropy bound $H(y)-\Phi_G(y)\le 8m(1-e^{-H(y)/m})$ is the statement $\mathcal D_m\le0$ on $\mathcal P(G)$. This theorem is the second-order optimality condition at a maximizer of the defect, tested along the curve of means of the score-tilted laws $p_M(1+t\,a(M))$; it compares with the actual maximum entropy $\Phi_G$ and not with any smooth surrogate. Rewritten in normalized coordinates it becomes a spectral inequality for the covariance matrix of the matching indicators under $p$.
--
--   **Formalization Note** The defect is `entropyDefect G m y` and $\Phi_G$ is `maxMatchingEntropy G`, defined via `sSup`. Coordinates with $x_e=0$ have $w_e=0$, and Lean's conventions $w_e^2/x_e=0/0=0$ and $\log0=0$ make their terms vanish. The point $x$ lies in $\mathcal P(G)$ automatically because it is the mean of $p$. The vertex type is not assumed finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/SecondVariation.lean#L52-L107

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
theorem OAI.MatchingEntropy.matching_defect_second_variation (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p = maxMatchingEntropy G x) {m : ℝ} (hm : m ≠ 0)
    (hmax : ∀ y ∈ G.polytope, entropyDefect G m y ≤ entropyDefect G m x)
    (u : E → ℝ) (c : ℝ) (hcenter : ∑ M, p M*linearScore G u c M = 0) :
    (8*Real.exp (-entropy x/m)-1)*
        (∑ e, (G.mean (fun M => p M*linearScore G u c M) e)^2/x e) +
      (8*Real.exp (-entropy x/m)/m)*
        (entropyLineD x (G.mean (fun M => p M*linearScore G u c M)) 0)^2 +
      (∑ M, p M*(linearScore G u c M)^2) ≤ 0 := by sorry
