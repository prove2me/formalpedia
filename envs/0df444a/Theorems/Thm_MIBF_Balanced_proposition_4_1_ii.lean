-- Prove2me | Theorems.Thm_MIBF_Balanced_proposition_4_1_ii
-- name    : MIBF.Balanced.proposition_4_1_ii
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:59:19.374466+00:00
-- url     : https://prove2.me/theorems/77a3250c-e020-4482-bb7a-026e6d50151c
-- title:
--   Proposition 4.1(ii) — $(e_1,e_2)\mapsto\kappa(\iota(e_1),\iota(e_2))$ is jointly convex on the open square, and its l.s.c. closure is convex on the closed square
-- statement:
--   Let $\tilde\kappa(e_1,e_2)=\kappa(\iota(e_1),\iota(e_2))$, where $\kappa$ is the residual of Proposition 4.1(i) and $\iota$ the lower inverse of the binary entropy (bits, so entropies range over $[0,1]$). Then:
--   1. $\tilde\kappa$ is jointly convex on the open square $(0,1)^2$;
--   2. its lower-semicontinuous closure $\bar\kappa(x)=\liminf_{y\to x,\,y\in(0,1)^2}\tilde\kappa(y)$, an extended-real function, is convex on the closed square $[0,1]^2$.
--
--   Together with the convexity of the perspective $F$, this gives the Jensen step of the four-moment lower bound $\zeta\ge L_1$ (Theorem 4.2).
--
--   **Formalization Note** Convexity of the extended-real closure is stated as convexity of its epigraph $\{(x,t)\in[0,1]^2\times\mathbb R:\ \bar\kappa(x)\le t\}$, the standard definition for functions with values in $(-\infty,+\infty]$; it avoids extended-real arithmetic.
--
--   Differences from the source:
--   - encoding: nats, open square $(0,\ln 2)^2$ and closed square $[0,\ln 2]^2$ → bits, $(0,1)^2$ and $[0,1]^2$; reason: $e\mapsto e/\ln 2$ is linear and $\tilde\kappa$ scales by $1/\ln 2$, so convexity is unchanged.
--   - encoding: "its lower-semicontinuous closure is convex" → the closure defined as the $\liminf$ from the open square, and convexity as convexity of its epigraph over $[0,1]^2$; reason: the lower-semicontinuous envelope and the epigraph definition of convexity for extended-valued functions.
-- source:
--   Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (held version, sha256 35793b82…1f9f), p. 11, Proposition 4.1(ii); proof [Full] Supplementary Theorem S.20.6

import Mathlib
import Definitions.Def_MIBF_Balanced_PureGap

namespace MIBF.Balanced
theorem proposition_4_1_ii :
    ConvexOn ℝ (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) (fun p : ℝ × ℝ => kappaEnt p.1 p.2) ∧
      Convex ℝ {q : (ℝ × ℝ) × ℝ | q.1 ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ∧
        kappaEntClosure q.1.1 q.1.2 ≤ ((q.2 : ℝ) : EReal)} := by sorry
end MIBF.Balanced
