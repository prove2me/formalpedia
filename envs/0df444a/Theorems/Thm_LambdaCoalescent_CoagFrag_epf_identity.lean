-- Prove2me | Theorems.Thm_LambdaCoalescent_CoagFrag_epf_identity
-- name    : LambdaCoalescent.CoagFrag.epf_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:56.150994+00:00
-- url     : https://prove2.me/theorems/b5d55e36-1504-4545-8c19-e88d1d20d4ab
-- title:
--   Proof of Theorem 12, p. 1898 — under (64), p_{α,θ}(a) p_{β,θ/α}(j) = ∏ p_{α,−αβ}(a_{i,·}) p_{αβ,θ}(b)
-- statement:
--   Let $0<\alpha<1$, $0\le\beta<1$ and $\theta>-\alpha\beta$. Let $\pi^1=\{A_1,\dots,A_K\}$ and $\pi^2=\{B_1,\dots,B_k\}$ be partitions of $[n]$ with $\pi^1$ a refinement of $\pi^2$; write $a_\ell=|A_\ell|$, $b_i=|B_i|$, $j_i$ for the number of blocks of $\pi^1$ inside $B_i$, and $a_{i,1},\dots,a_{i,j_i}$ for their sizes. With $p_{\alpha,\theta}$ the EPF (15),
--   $$p_{\alpha,\theta}(a_1,\dots,a_K)\;p_{\beta,\theta/\alpha}(j_1,\dots,j_k)=\prod_{i=1}^{k}p_{\alpha,-\alpha\beta}(a_{i,1},\dots,a_{i,j_i})\;p_{\alpha\beta,\theta}(b_1,\dots,b_k).$$
--
--   This is the display in the proof of Theorem 12 with the parameters (64): $(\alpha_c,\theta_c)=(\beta,\theta/\alpha)$, $(\alpha_1,\theta_1)=(\alpha\beta,\theta)$, $(\alpha_f,\theta_f)=(\alpha,-\alpha\beta)$, of which the paper says "this equality is evident by inspection". By Lemmas 34 and 35 it is the statement that the two joint laws of Theorem 12 agree on every $[n]$.
--
--   **Formalization Note** The EPFs are the cancelled form of the Setting module, so the case $\beta=0$ (where $\theta_f=-\alpha\beta=0$) is covered. $\alpha>0$ makes $\theta/\alpha$ meaningful. Block sizes, counts and nested sizes are multisets.
-- source:
--   Pitman, Coalescents with multiple collisions, Ann. Probab. 27 (1999), p. 1898, proof of Theorem 12, the display after (64) and "If (64) holds, this equality is evident by inspection"

import Mathlib
import Definitions.Def_LambdaCoalescent_CoagFrag_Setting

namespace LambdaCoalescent.CoagFrag

theorem epf_identity (α β θ : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ : -(α * β) < θ) (n : ℕ) (π₁ π₂ : Setoid (Fin n)) (h : π₁ ≤ π₂) :
    pdEPF α θ (blockSizes π₁) * pdEPF β (θ / α) (coagCounts π₁ π₂) =
      ((fragSizes π₁ π₂).map (pdEPF α (-(α * β)))).prod * pdEPF (α * β) θ (blockSizes π₂) := by sorry

end LambdaCoalescent.CoagFrag
