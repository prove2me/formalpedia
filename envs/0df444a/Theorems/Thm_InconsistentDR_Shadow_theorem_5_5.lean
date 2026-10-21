-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_theorem_5_5
-- name    : InconsistentDR.Shadow.theorem_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:26.983993+00:00
-- url     : https://prove2.me/theorems/d9a765ad-d7af-477b-9d8b-228a977f2e15
-- title:
--   Theorem 5.5 (ii), (ix), p. 20 — (J_A Tⁿx + nv_R, J_{A⁻¹}Tⁿx + nv_D) is bounded, and Fejér monotone w.r.t. Z × K after a shift
-- statement:
--   Throughout, $X$ is a real Hilbert space, $A, B : X \rightrightarrows X$ are maximally monotone, $J_A = (\mathrm{Id}+A)^{-1}$ and $J_B$ are their resolvents, $R_A = 2J_A - \mathrm{Id}$, $J_{A^{-1}} = \mathrm{Id} - J_A$ and $J_{B^{-1}} = \mathrm{Id} - J_B$, and
--   $$T = \mathrm{Id} - J_A + J_B R_A$$
--   is the Douglas–Rachford operator. The vectors $v = P_{\overline{\operatorname{ran}}(\mathrm{Id}-T)}(0)$, $v_D = P_{\overline{D}}(0)$ and $v_R = P_{\overline{R}}(0)$ are the projections of $0$ onto the closures of $\operatorname{ran}(\mathrm{Id}-T)$, $D = \operatorname{dom}A - \operatorname{dom}B$ and $R = \operatorname{ran}A + \operatorname{ran}B$, and the standing assumption (12) of the paper is in force:
--   $$\overline{\operatorname{ran}}(\mathrm{Id}-T) = \overline{D\cap R} = \overline{D}\cap\overline{R}.$$
--
--   Suppose that $\operatorname{Fix}(v + T) \neq \varnothing$ and let $x \in X$. Let $Z$ be the primal and $K = \{k \mid \exists z,\ k \in -v + Az,\ -k \in B(z - v)\}$ the dual solution set of the normal problem. Then:
--   1. (ii) the sequence $(J_A T^n x + n v_R,\ J_{A^{-1}} T^n x + n v_D)_{n\in\mathbb N}$ is bounded;
--   2. (ix) if $A$ and $B$ are paramonotone, the sequence
--   $$\big((0, -v) + (J_A T^n x + n v_R,\ J_{A^{-1}} T^n x + n v_D)\big)_{n\in\mathbb N}$$
--   is Fejér monotone with respect to $Z \times K$ in the Hilbert space $X \times X$.
--
--   Fejér monotonicity with respect to $Z\times K$ is the property that Proposition 6.6 combines with an Opial-type argument to obtain weak convergence of the shadows.
--
--   **Formalization Note** The resolvents are maps `JA JB : X → X` characterized by `IsResolvent 1 A JA` ($x - J_A x \in A(J_A x)$ for every $x$, which is $J_A = (\mathrm{Id}+A)^{-1}$; for maximally monotone $A$ such a map exists and is unique). $J_{A^{-1}}$ is written `resInv JA` $= \mathrm{Id} - J_A$, by the inverse resolvent identity (8). The projections $v, v_D, v_R$ are encoded as least-norm points of the respective closures (these closures are nonempty, closed and convex, so the least-norm point is the projection of $0$). The standing assumption (12) of p. 6 is an explicit hypothesis, and `CompleteSpace X` makes the inner product space a Hilbert space. Boundedness of the pair sequence is stated as boundedness of both coordinate sequences (equivalent). Fejér monotonicity uses `IsFejerPair`, which writes the Hilbert norm of $X \times X$ as $\|a\|^2 + \|b\|^2$.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), p. 20, Theorem 5.5 (ii), (ix)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_InconsistentDR_Shadow_Operators

namespace InconsistentDR.Shadow

open scoped InnerProductSpace
open ThreeOpSplitting.Convergence

/-- Theorem 5.5 (ii), (ix), p. 20, under (12), when `Fix(v + T) ≠ ∅`:
(ii) `(J_A Tⁿx + n v_R, J_{A⁻¹} Tⁿx + n v_D)ₙ` is bounded;
(ix) if `A`, `B` are paramonotone, `((0, −v) + (J_A Tⁿx + n v_R, J_{A⁻¹} Tⁿx + n v_D))ₙ` is Fejér
monotone with respect to `Z × K` (Hilbert norm of `X × X`). -/
theorem theorem_5_5 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (A B : X → Set X) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (JA JB : X → X) (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB)
    (v vD vR : X)
    (hv : IsMinNormPt (closure (Set.range fun x => x - drT JA JB x)) v)
    (hvD : IsMinNormPt (closure (setD A B)) vD) (hvR : IsMinNormPt (closure (setR A B)) vR)
    (h12 : Standing12 A B JA JB)
    (hfix : (FixSet fun y => v + drT JA JB y).Nonempty) (x : X) :
    (Bornology.IsBounded (Set.range fun n : ℕ => JA ((drT JA JB)^[n] x) + (n : ℝ) • vR) ∧
      Bornology.IsBounded
        (Set.range fun n : ℕ => resInv JA ((drT JA JB)^[n] x) + (n : ℝ) • vD)) ∧
    (IsParamonotone A → IsParamonotone B →
      IsFejerPair (fun n => JA ((drT JA JB)^[n] x) + (n : ℝ) • vR)
        (fun n => -v + (resInv JA ((drT JA JB)^[n] x) + (n : ℝ) • vD))
        (solZ A B v ×ˢ solK A B v)) := by sorry

end InconsistentDR.Shadow
