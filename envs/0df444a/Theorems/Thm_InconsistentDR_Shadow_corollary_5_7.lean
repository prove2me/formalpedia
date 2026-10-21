-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_corollary_5_7
-- name    : InconsistentDR.Shadow.corollary_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:36.831056+00:00
-- url     : https://prove2.me/theorems/024d4ca8-2f71-455d-b38d-215b56793669
-- title:
--   Corollary 5.7 (ii), (iii), p. 21 — if v_R = 0 and Fix(v + T) ≠ ∅, the primal shadows J_A Tⁿx and J_B R_A Tⁿx are bounded
-- statement:
--   Throughout, $X$ is a real Hilbert space, $A, B : X \rightrightarrows X$ are maximally monotone, $J_A = (\mathrm{Id}+A)^{-1}$ and $J_B$ are their resolvents, $R_A = 2J_A - \mathrm{Id}$, $J_{A^{-1}} = \mathrm{Id} - J_A$ and $J_{B^{-1}} = \mathrm{Id} - J_B$, and
--   $$T = \mathrm{Id} - J_A + J_B R_A$$
--   is the Douglas–Rachford operator. The vectors $v = P_{\overline{\operatorname{ran}}(\mathrm{Id}-T)}(0)$, $v_D = P_{\overline{D}}(0)$ and $v_R = P_{\overline{R}}(0)$ are the projections of $0$ onto the closures of $\operatorname{ran}(\mathrm{Id}-T)$, $D = \operatorname{dom}A - \operatorname{dom}B$ and $R = \operatorname{ran}A + \operatorname{ran}B$, and the standing assumption (12) of the paper is in force:
--   $$\overline{\operatorname{ran}}(\mathrm{Id}-T) = \overline{D\cap R} = \overline{D}\cap\overline{R}.$$
--
--   Suppose that $v_R = 0$ and $\operatorname{Fix}(v + T) \neq \varnothing$, and let $x \in X$. Then
--   1. $(J_A T^n x)_{n\in\mathbb N}$ is bounded;
--   2. $(J_B R_A T^n x)_{n\in\mathbb N}$ is bounded.
--
--   Although the governing sequence $T^n x$ diverges when $v \neq 0$, its primal shadows stay bounded; this is the compactness behind the weak convergence of Proposition 6.6.
--
--   **Formalization Note** The resolvents are maps `JA JB : X → X` characterized by `IsResolvent 1 A JA` ($x - J_A x \in A(J_A x)$ for every $x$, which is $J_A = (\mathrm{Id}+A)^{-1}$; for maximally monotone $A$ such a map exists and is unique). $J_{A^{-1}}$ is written `resInv JA` $= \mathrm{Id} - J_A$, by the inverse resolvent identity (8). The projections $v, v_D, v_R$ are encoded as least-norm points of the respective closures (these closures are nonempty, closed and convex, so the least-norm point is the projection of $0$). The standing assumption (12) of p. 6 is an explicit hypothesis, and `CompleteSpace X` makes the inner product space a Hilbert space.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), p. 21, Corollary 5.7 (ii), (iii)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_InconsistentDR_Shadow_Operators

namespace InconsistentDR.Shadow

open scoped InnerProductSpace
open ThreeOpSplitting.Convergence

/-- Corollary 5.7 (ii), (iii), p. 21, under (12): if `v_R = 0` and `Fix(v + T) ≠ ∅`, then the
primal shadows `(J_A Tⁿx)ₙ` and `(J_B R_A Tⁿx)ₙ` are bounded. -/
theorem corollary_5_7 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (A B : X → Set X) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (JA JB : X → X) (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB)
    (v vD vR : X)
    (hv : IsMinNormPt (closure (Set.range fun x => x - drT JA JB x)) v)
    (hvD : IsMinNormPt (closure (setD A B)) vD) (hvR : IsMinNormPt (closure (setR A B)) vR)
    (h12 : Standing12 A B JA JB)
    (hvR0 : vR = 0) (hfix : (FixSet fun y => v + drT JA JB y).Nonempty) (x : X) :
    Bornology.IsBounded (Set.range fun n : ℕ => JA ((drT JA JB)^[n] x)) ∧
      Bornology.IsBounded (Set.range fun n : ℕ => JB (refl JA ((drT JA JB)^[n] x))) := by sorry

end InconsistentDR.Shadow
