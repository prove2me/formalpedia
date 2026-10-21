-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_proposition_4_2
-- name    : InconsistentDR.Shadow.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:23.552244+00:00
-- url     : https://prove2.me/theorems/9d94e153-230f-48e8-8fba-39e2632aa9d3
-- title:
--   Proposition 4.2, p. 13 — moving a normal-problem pair (x, x*) along v_D and v_R keeps it a solution pair
-- statement:
--   Throughout, $X$ is a real Hilbert space, $A, B : X \rightrightarrows X$ are maximally monotone, $J_A = (\mathrm{Id}+A)^{-1}$ and $J_B$ are their resolvents, $R_A = 2J_A - \mathrm{Id}$, $J_{A^{-1}} = \mathrm{Id} - J_A$ and $J_{B^{-1}} = \mathrm{Id} - J_B$, and
--   $$T = \mathrm{Id} - J_A + J_B R_A$$
--   is the Douglas–Rachford operator. The vectors $v = P_{\overline{\operatorname{ran}}(\mathrm{Id}-T)}(0)$, $v_D = P_{\overline{D}}(0)$ and $v_R = P_{\overline{R}}(0)$ are the projections of $0$ onto the closures of $\operatorname{ran}(\mathrm{Id}-T)$, $D = \operatorname{dom}A - \operatorname{dom}B$ and $R = \operatorname{ran}A + \operatorname{ran}B$, and the standing assumption (12) of the paper is in force:
--   $$\overline{\operatorname{ran}}(\mathrm{Id}-T) = \overline{D\cap R} = \overline{D}\cap\overline{R}.$$
--
--   Let $\alpha \ge 0$, $\beta \le 0$ and $(x, x^*) \in X \times X$ with $x^* \in (v - Ax) \cap B(x - v)$. Then
--   1. $x^* + \alpha v_D \in (v - Ax) \cap B(x - v)$;
--   2. $x + \beta v_R \in A^{-1}(-x^* + v) \cap (v + B^{-1}x^*)$;
--   3. $x^* \in (v - \alpha v_D - Ax) \cap B(x + \beta v_R - v)$.
--
--   The statement shows that $v_D$ is a recession direction of the dual solutions and $v_R$ of the primal solutions of the normal problem.
--
--   **Formalization Note** The resolvents are maps `JA JB : X → X` characterized by `IsResolvent 1 A JA` ($x - J_A x \in A(J_A x)$ for every $x$, which is $J_A = (\mathrm{Id}+A)^{-1}$; for maximally monotone $A$ such a map exists and is unique). $J_{A^{-1}}$ is written `resInv JA` $= \mathrm{Id} - J_A$, by the inverse resolvent identity (8). The projections $v, v_D, v_R$ are encoded as least-norm points of the respective closures (these closures are nonempty, closed and convex, so the least-norm point is the projection of $0$). The standing assumption (12) of p. 6 is an explicit hypothesis, and `CompleteSpace X` makes the inner product space a Hilbert space. Memberships in inverse operators are written directly: $y \in A^{-1}u$ as $u \in Ay$, and $y \in v + B^{-1}x^*$ as $x^* \in B(y - v)$.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), p. 13, Proposition 4.2

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_InconsistentDR_Shadow_Operators

namespace InconsistentDR.Shadow

open scoped InnerProductSpace
open ThreeOpSplitting.Convergence

/-- Proposition 4.2, p. 13, under (12). Let `α ≥ 0`, `β ≤ 0`, and `x* ∈ (v − A x) ∩ B(x − v)`
(written `xs`). Then (i) `x* + α v_D ∈ (v − A x) ∩ B(x − v)`;
(ii) `x + β v_R ∈ A⁻¹(−x* + v) ∩ (v + B⁻¹ x*)`; (iii) `x* ∈ (v − α v_D − A x) ∩ B(x + β v_R − v)`. -/
theorem proposition_4_2 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (A B : X → Set X) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (JA JB : X → X) (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB)
    (v vD vR : X)
    (hv : IsMinNormPt (closure (Set.range fun x => x - drT JA JB x)) v)
    (hvD : IsMinNormPt (closure (setD A B)) vD) (hvR : IsMinNormPt (closure (setR A B)) vR)
    (h12 : Standing12 A B JA JB)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : β ≤ 0) (x xs : X) (h1 : v - xs ∈ A x) (h2 : xs ∈ B (x - v)) :
    (v - (xs + α • vD) ∈ A x ∧ xs + α • vD ∈ B (x - v)) ∧
    (v - xs ∈ A (x + β • vR) ∧ xs ∈ B (x + β • vR - v)) ∧
    (v - α • vD - xs ∈ A x ∧ xs ∈ B (x + β • vR - v)) := by sorry

end InconsistentDR.Shadow
