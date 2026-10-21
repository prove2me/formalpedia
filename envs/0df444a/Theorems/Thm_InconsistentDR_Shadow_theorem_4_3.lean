-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_theorem_4_3
-- name    : InconsistentDR.Shadow.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:32.149915+00:00
-- url     : https://prove2.me/theorems/0625c3ed-9fe2-4bcd-84d8-62ba9e91706b
-- title:
--   Theorem 4.3, p. 14 — Z̃ = {x | 0 ∈ −v_R + Ax + B(x − v_D)} ⊆ Z, with equality when v_R = 0
-- statement:
--   Throughout, $X$ is a real Hilbert space, $A, B : X \rightrightarrows X$ are maximally monotone, $J_A = (\mathrm{Id}+A)^{-1}$ and $J_B$ are their resolvents, $R_A = 2J_A - \mathrm{Id}$, $J_{A^{-1}} = \mathrm{Id} - J_A$ and $J_{B^{-1}} = \mathrm{Id} - J_B$, and
--   $$T = \mathrm{Id} - J_A + J_B R_A$$
--   is the Douglas–Rachford operator. The vectors $v = P_{\overline{\operatorname{ran}}(\mathrm{Id}-T)}(0)$, $v_D = P_{\overline{D}}(0)$ and $v_R = P_{\overline{R}}(0)$ are the projections of $0$ onto the closures of $\operatorname{ran}(\mathrm{Id}-T)$, $D = \operatorname{dom}A - \operatorname{dom}B$ and $R = \operatorname{ran}A + \operatorname{ran}B$, and the standing assumption (12) of the paper is in force:
--   $$\overline{\operatorname{ran}}(\mathrm{Id}-T) = \overline{D\cap R} = \overline{D}\cap\overline{R}.$$
--
--   Let $Z = \{x \mid 0 \in -v + Ax + B(x - v)\}$ be the solution set of the normal problem and set
--   $$\widetilde Z = \{x \in X \mid 0 \in -v_R + Ax + B(x - v_D)\}.$$
--   Then
--   1. $\widetilde Z \subseteq Z$;
--   2. if $v_R = 0$, then $\widetilde Z = Z$.
--
--   When $v_R = 0$ the normal problem therefore reduces to $0 \in Ax + B(x - v_D)$, a problem with no linear perturbation; this is what makes $Z$ a set of minimizers in the optimization setting of §6.
--
--   **Formalization Note** The resolvents are maps `JA JB : X → X` characterized by `IsResolvent 1 A JA` ($x - J_A x \in A(J_A x)$ for every $x$, which is $J_A = (\mathrm{Id}+A)^{-1}$; for maximally monotone $A$ such a map exists and is unique). $J_{A^{-1}}$ is written `resInv JA` $= \mathrm{Id} - J_A$, by the inverse resolvent identity (8). The projections $v, v_D, v_R$ are encoded as least-norm points of the respective closures (these closures are nonempty, closed and convex, so the least-norm point is the projection of $0$). The standing assumption (12) of p. 6 is an explicit hypothesis, and `CompleteSpace X` makes the inner product space a Hilbert space.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), p. 14, Theorem 4.3, (50)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_InconsistentDR_Shadow_Operators

namespace InconsistentDR.Shadow

open scoped InnerProductSpace
open ThreeOpSplitting.Convergence

/-- Theorem 4.3, p. 14, under (12). With `Z̃ := {x | 0 ∈ −v_R + A x + B(x − v_D)}` (50):
(i) `Z̃ ⊆ Z`; (ii) if `v_R = 0` then `Z̃ = Z`. -/
theorem theorem_4_3 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (A B : X → Set X) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (JA JB : X → X) (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB)
    (v vD vR : X)
    (hv : IsMinNormPt (closure (Set.range fun x => x - drT JA JB x)) v)
    (hvD : IsMinNormPt (closure (setD A B)) vD) (hvR : IsMinNormPt (closure (setR A B)) vR)
    (h12 : Standing12 A B JA JB) :
    {x | ∃ a ∈ A x, ∃ b ∈ B (x - vD), -vR + a + b = 0} ⊆ solZ A B v ∧
    (vR = 0 → {x | ∃ a ∈ A x, ∃ b ∈ B (x - vD), -vR + a + b = 0} = solZ A B v) := by sorry

end InconsistentDR.Shadow
