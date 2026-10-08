-- Prove2me | Theorems.Thm_NesterovRCD_Adaptive_eq_6_4
-- name    : NesterovRCD.Adaptive.eq_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:28.613068+00:00
-- url     : https://prove2.me/theorems/621c419c-b30a-4002-b6cc-af08850a4fd2
-- title:
--   (6.4) — the doubling loop of RACDM terminates with $\hat L_i\le 2L_i$
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be differentiable with coordinate-wise Lipschitz partial derivatives (2.2): for every $i$, $x$ and $u\in\mathbb R$,
--   $$|\nabla_i f(x+ue_i)-\nabla_i f(x)|\le L_i|u| .$$
--   Fix a point $x$, a coordinate $i$ and an estimate $\ell$ with $0<\ell\le L_i$. Then the doubling loop of RACDM (6.1) started at $x$, $i$, $\ell$ terminates: some $d\ge0$ satisfies $\nabla_i f(x)\cdot\nabla_i f(x-(2^d\ell)^{-1}\nabla_if(x)e_i)\ge0$. Moreover the accepted estimate satisfies
--   $$2^{d(x,i,\ell)}\,\ell\ \le\ 2L_i ,$$
--   where $d(x,i,\ell)$ is the number of doublings (the least such $d$).
--
--   This is the bound (6.4) of the proof of Theorem 7: once the estimate exceeds $L_i$ the sign test is passed, so the loop never overshoots $L_i$ by more than a factor $2$. It gives both that the method is well defined and the factor that enters the decrease bound $3/(8L_i)$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` (scalar coordinates: the paper sets $N=n$ in §6.1), coordinates are indexed $0,\dots,n-1$ for the paper's $1,\dots,n$, and the gradient is an explicit map $g$ with $g(x)=\nabla f(x)$, as in the published definition `ConvexOptAlg_CoordDescent_Defs` that this mission reuses (its `IsCoordSmooth f g L` is (2.2) with one-dimensional blocks and $|\cdot|$ as block norm; it includes differentiability). The paper states (6.4) for "the internal cycle" with the entry assumption $\hat L_{i_k}\le L_{i_k}$; we state it for an arbitrary entry point $x$, coordinate $i$ and entry estimate $0<\ell\le L_i$ (positivity is implicit in the paper: the method divides by $\hat L_i$). Every intermediate estimate $2^{d'}\ell$, $d'\le d$, is at most the accepted one, so the bound on the accepted one is the bound "during the internal cycle". Convexity is not needed and not assumed.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 18, proof of Theorem 7, (6.4)

import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs
import Definitions.Def_NesterovRCD_Adaptive_RACDM

namespace NesterovRCD.Adaptive

open ConvexOptAlg.CoordDescent

/-- (6.4), p. 18: if the inner cycle of RACDM (6.1) is entered on coordinate `i` at `x` with an
estimate `0 < ℓ ≤ L_i`, the cycle terminates, and the accepted estimate `2^d ℓ` satisfies
`L̂_i ≤ 2 L_i`. -/
theorem eq_6_4 {n : ℕ} (f : Vec n → ℝ) (g : Vec n → Vec n) (L : Fin n → ℝ)
    (hL : IsCoordSmooth f g L) (x : Vec n) (i : Fin n) (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓL : ℓ ≤ L i) :
    (∃ d : ℕ, ¬ (g x i * g (trial g x i (2 ^ d * ℓ)) i < 0)) ∧
      2 ^ doublings g x i ℓ * ℓ ≤ 2 * L i := by sorry

end NesterovRCD.Adaptive
