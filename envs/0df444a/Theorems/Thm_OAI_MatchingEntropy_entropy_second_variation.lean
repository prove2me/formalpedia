-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_entropy_second_variation
-- name    : OAI.MatchingEntropy.entropy_second_variation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:04:28.125925+00:00
-- url     : https://prove2.me/theorems/85ec1230-9fdb-4c13-b8dd-5602151c6904
-- title:
--   Second-order condition for the entropy barrier along a line minus a log-partition function
-- statement:
--   Let $\iota$ and $\kappa$ be finite sets. For $z\in\mathbb R^\iota$ write $H(z)=-\sum_{i\in\iota}z_i\log z_i$ (with $0\log 0=0$). For $m\neq0$ the *entropy barrier* is
--
--   $$
--   B_m(h)=h-8m\big(1-e^{-h/m}\big).
--   $$
--
--   Let $x,v\in\mathbb R^\iota$ with $v_i=0$ whenever $x_i=0$, and put $D=-\sum_i v_i\log x_i-\sum_i v_i$, the derivative of $t\mapsto H(x+tv)$ at $t=0$. Let $p$ be a probability vector on $\kappa$ and $a\in\mathbb R^\kappa$ a centered score, $\sum_k p_k a_k=0$; let $\sigma^2=\sum_k p_k a_k^2$ and $Z_p(a,t)=\sum_k p_k e^{t a_k}$. Let $m\neq0$ and $c_0,c_1\in\mathbb R$, and suppose that $t=0$ is a local maximum of
--
--   $$
--   \psi(t)=B_m\big(H(x+tv)\big)+c_0+c_1t+\sigma^2t^2-\log Z_p(a,t).
--   $$
--
--   Then
--
--   $$
--   \big(8e^{-H(x)/m}-1\big)\sum_{i\in\iota}\frac{v_i^2}{x_i}\;+\;\frac{8e^{-H(x)/m}}{m}\,D^2\;+\;\sum_{k\in\kappa}p_k a_k^2\;\le\;0 .
--   $$
--
--   The left side is exactly $\psi''(0)$, so this is the second-order necessary condition for a local maximum, written out explicitly. The barrier $B_m$ is the one in the matching entropy bound $H(y)-\Phi_G(y)\le 8m(1-e^{-H(y)/m})$, which says $B_m(H(y))\le\Phi_G(y)$ when $\Phi_G(y)$ denotes the maximum entropy of a law on the perfect matchings of a graph $G$ with edge marginals $y$; the theorem is applied with $x$ a maximizer of the entropy defect, $v$ a variation of the edge marginals and $a$ a score on perfect matchings.
--
--   **Formalization Note** The vector $x$ is not required to be nonnegative (for negative arguments Mathlib's logarithm is $\log|z|$). The terms with $x_i=0$ vanish because $v_i=0$ there: Lean's conventions give $v_i^2/x_i=0/0=0$ and $\log 0=0$. The barrier is `entropyBarrier m`, the quantity $D$ is `entropyLineD x v 0`, and $Z_p(a,t)$ is `partition p a t`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Calculus.lean#L214-L247

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter

theorem OAI.MatchingEntropy.entropy_second_variation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x v : ι → ℝ) (hsupp : ∀ i, x i = 0 → v i = 0)
    {p : κ → ℝ} (hp : p ∈ probabilitySimplex κ) (a : κ → ℝ)
    (hcenter : ∑ i, p i*a i = 0) {m : ℝ} (hm : m ≠ 0) (c₀ c₁ : ℝ)
    (hlocal : IsLocalMax (fun t => entropyBarrier m (entropy (fun i => x i+t*v i)) +
      c₀+t*c₁+t^2*(∑ i, p i*(a i)^2)-Real.log (partition p a t)) 0) :
    (8*Real.exp (-entropy x/m)-1)*(∑ i, (v i)^2/x i) +
      (8*Real.exp (-entropy x/m)/m)*(entropyLineD x v 0)^2 +
      (∑ i, p i*(a i)^2) ≤ 0 := by sorry
