-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_proposition_3_3
-- name    : InconsistentDR.Shadow.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:21.535958+00:00
-- url     : https://prove2.me/theorems/882593bf-2299-40a9-93e6-b207254e462e
-- title:
--   Proposition 3.3 (v), (vii), (viii), p. 10 — ⟨v_D, v_R⟩ = 0, v = v_D + v_R, ‖v‖² = ‖v_D‖² + ‖v_R‖²
-- statement:
--   Throughout, $X$ is a real Hilbert space, $A, B : X \rightrightarrows X$ are maximally monotone, $J_A = (\mathrm{Id}+A)^{-1}$ and $J_B$ are their resolvents, $R_A = 2J_A - \mathrm{Id}$, $J_{A^{-1}} = \mathrm{Id} - J_A$ and $J_{B^{-1}} = \mathrm{Id} - J_B$, and
--   $$T = \mathrm{Id} - J_A + J_B R_A$$
--   is the Douglas–Rachford operator. The vectors $v = P_{\overline{\operatorname{ran}}(\mathrm{Id}-T)}(0)$, $v_D = P_{\overline{D}}(0)$ and $v_R = P_{\overline{R}}(0)$ are the projections of $0$ onto the closures of $\operatorname{ran}(\mathrm{Id}-T)$, $D = \operatorname{dom}A - \operatorname{dom}B$ and $R = \operatorname{ran}A + \operatorname{ran}B$, and the standing assumption (12) of the paper is in force:
--   $$\overline{\operatorname{ran}}(\mathrm{Id}-T) = \overline{D\cap R} = \overline{D}\cap\overline{R}.$$
--
--   Then
--   1. $\langle v_D, v_R\rangle = 0$;
--   2. $v = v_D + v_R$;
--   3. $$\|v\|^2 = \|v_D\|^2 + \|v_R\|^2 .$$
--
--   The minimal displacement vector $v$ of the Douglas–Rachford operator thus splits orthogonally into a "domain" part $v_D$ and a "range" part $v_R$; the main theorem works in the case $v_R = 0$, where $v = v_D$.
--
--   **Formalization Note** The resolvents are maps `JA JB : X → X` characterized by `IsResolvent 1 A JA` ($x - J_A x \in A(J_A x)$ for every $x$, which is $J_A = (\mathrm{Id}+A)^{-1}$; for maximally monotone $A$ such a map exists and is unique). $J_{A^{-1}}$ is written `resInv JA` $= \mathrm{Id} - J_A$, by the inverse resolvent identity (8). The projections $v, v_D, v_R$ are encoded as least-norm points of the respective closures (these closures are nonempty, closed and convex, so the least-norm point is the projection of $0$). The standing assumption (12) of p. 6 is an explicit hypothesis, and `CompleteSpace X` makes the inner product space a Hilbert space. The last equality of (viii), $\|v_D\|^2 + \|v_R\|^2 = \|(v_R, v_D)\|^2$, is the definition of the Hilbert norm of $X \times X$ and is omitted.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), p. 10, Proposition 3.3 (v), (vii), (viii)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_InconsistentDR_Shadow_Operators

namespace InconsistentDR.Shadow

open scoped InnerProductSpace
open ThreeOpSplitting.Convergence

/-- Proposition 3.3 (v), (vii), (viii), p. 10, under the standing assumption (12):
`⟨v_D, v_R⟩ = 0`, `v = v_D + v_R`, `‖v‖² = ‖v_D‖² + ‖v_R‖²`. -/
theorem proposition_3_3 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (A B : X → Set X) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (JA JB : X → X) (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB)
    (v vD vR : X)
    (hv : IsMinNormPt (closure (Set.range fun x => x - drT JA JB x)) v)
    (hvD : IsMinNormPt (closure (setD A B)) vD) (hvR : IsMinNormPt (closure (setR A B)) vR)
    (h12 : Standing12 A B JA JB) :
    ⟪vD, vR⟫_ℝ = 0 ∧ v = vD + vR ∧ ‖v‖ ^ 2 = ‖vD‖ ^ 2 + ‖vR‖ ^ 2 := by sorry

end InconsistentDR.Shadow
