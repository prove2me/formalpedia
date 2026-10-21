-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_proposition_5_3
-- name    : InconsistentDR.Shadow.proposition_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:30.667266+00:00
-- url     : https://prove2.me/theorems/7ffc408c-92af-4a2f-928e-efbbf6ce8dbe
-- title:
--   Proposition 5.3, p. 19 — on Fix(v + T): Tⁿf = f − nv, and the shadows move by −nv_R, −nv_D
-- statement:
--   Throughout, $X$ is a real Hilbert space, $A, B : X \rightrightarrows X$ are maximally monotone, $J_A = (\mathrm{Id}+A)^{-1}$ and $J_B$ are their resolvents, $R_A = 2J_A - \mathrm{Id}$, $J_{A^{-1}} = \mathrm{Id} - J_A$ and $J_{B^{-1}} = \mathrm{Id} - J_B$, and
--   $$T = \mathrm{Id} - J_A + J_B R_A$$
--   is the Douglas–Rachford operator. The vectors $v = P_{\overline{\operatorname{ran}}(\mathrm{Id}-T)}(0)$, $v_D = P_{\overline{D}}(0)$ and $v_R = P_{\overline{R}}(0)$ are the projections of $0$ onto the closures of $\operatorname{ran}(\mathrm{Id}-T)$, $D = \operatorname{dom}A - \operatorname{dom}B$ and $R = \operatorname{ran}A + \operatorname{ran}B$, and the standing assumption (12) of the paper is in force:
--   $$\overline{\operatorname{ran}}(\mathrm{Id}-T) = \overline{D\cap R} = \overline{D}\cap\overline{R}.$$
--
--   Let $p \in \operatorname{Fix}(v + T)$ and $n \in \mathbb N$. Then
--   1. $T^n p = p - n v$;
--   2. $J_A T^n p = J_A p - n v_R$;
--   3. $J_{A^{-1}} T^n p = J_{A^{-1}} p - n v_D$;
--   4. $J_B R_A T^n p = J_B R_A p - n v_R$;
--   5. $$J_{B^{-1}} R_A T^n p = J_{B^{-1}} R_A p + n v_D .$$
--
--   These closed forms along the "straight-line" orbits of $T$ are the reference against which general orbits are compared in Theorem 5.5.
--
--   **Formalization Note** The resolvents are maps `JA JB : X → X` characterized by `IsResolvent 1 A JA` ($x - J_A x \in A(J_A x)$ for every $x$, which is $J_A = (\mathrm{Id}+A)^{-1}$; for maximally monotone $A$ such a map exists and is unique). $J_{A^{-1}}$ is written `resInv JA` $= \mathrm{Id} - J_A$, by the inverse resolvent identity (8). The projections $v, v_D, v_R$ are encoded as least-norm points of the respective closures (these closures are nonempty, closed and convex, so the least-norm point is the projection of $0$). The standing assumption (12) of p. 6 is an explicit hypothesis, and `CompleteSpace X` makes the inner product space a Hilbert space. The paper calls the fixed point $f$; it is named $p$ here. The printed "let $x \in X$" plays no role in the statement and is omitted.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), p. 19, Proposition 5.3

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_InconsistentDR_Shadow_Operators

namespace InconsistentDR.Shadow

open scoped InnerProductSpace
open ThreeOpSplitting.Convergence

/-- Proposition 5.3, p. 19, under (12). For `p ∈ Fix(v + T)` (the paper's `f`) and `n ∈ ℕ`:
(i) `Tⁿ p = p − n v`; (ii) `J_A Tⁿ p = J_A p − n v_R`; (iii) `J_{A⁻¹} Tⁿ p = J_{A⁻¹} p − n v_D`;
(iv) `J_B R_A Tⁿ p = J_B R_A p − n v_R`; (v) `J_{B⁻¹} R_A Tⁿ p = J_{B⁻¹} R_A p + n v_D`. -/
theorem proposition_5_3 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (A B : X → Set X) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (JA JB : X → X) (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB)
    (v vD vR : X)
    (hv : IsMinNormPt (closure (Set.range fun x => x - drT JA JB x)) v)
    (hvD : IsMinNormPt (closure (setD A B)) vD) (hvR : IsMinNormPt (closure (setR A B)) vR)
    (h12 : Standing12 A B JA JB)
    (p : X) (hp : p ∈ FixSet (fun y => v + drT JA JB y)) (n : ℕ) :
    (drT JA JB)^[n] p = p - (n : ℝ) • v ∧
    JA ((drT JA JB)^[n] p) = JA p - (n : ℝ) • vR ∧
    resInv JA ((drT JA JB)^[n] p) = resInv JA p - (n : ℝ) • vD ∧
    JB (refl JA ((drT JA JB)^[n] p)) = JB (refl JA p) - (n : ℝ) • vR ∧
    resInv JB (refl JA ((drT JA JB)^[n] p)) = resInv JB (refl JA p) + (n : ℝ) • vD := by sorry

end InconsistentDR.Shadow
