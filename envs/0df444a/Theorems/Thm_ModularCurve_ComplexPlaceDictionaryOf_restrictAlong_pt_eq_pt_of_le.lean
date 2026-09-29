-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_eq_pt_of_le
-- name    : ModularCurve.ComplexPlaceDictionaryOf.restrictAlong_pt_eq_pt_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/ea95dde7-0092-5ae5-acb2-f1829ad464b3
-- title:
--   Restriction of places along a q-expansion field inclusion
-- statement:
--   Let $\Gamma' \le \Gamma$ be subgroups of $\mathrm{SL}_2(\mathbb{Z})$ with $T = \begin{pmatrix}1&1\\0&1\end{pmatrix} \in \Gamma'$, and let $F_0, F_0'$ be intermediate fields of $\mathbb{Q}((q))/\mathbb{Q}$ with $F_0$ equal to [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101), the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the quotients $\mathrm{intSeriesC}\,p_f/\mathrm{intSeriesC}\,p_g$ attached to integral $q$-expansions $p_f, p_g$ of modular forms $f, g$ of a common weight on $\Gamma$ (with $\mathrm{intSeriesC}\,p_g \ne 0$). Write $\mathbb{C}\!\cdot\!F_0 \subseteq \mathbb{C}((q))$ for the subfield generated over $\mathbb{C}$ by the coefficientwise image of $F_0$, and likewise for $F_0'$. Let $D$ and $D'$ be complex place dictionaries for $(\Gamma, F_0)$ and $(\Gamma', F_0')$: each attaches to $\tau$ in the upper half-plane a place $\mathrm{pt}(\tau)$ of $\mathbb{C}\!\cdot\!F_0$ (resp. $\mathbb{C}\!\cdot\!F_0'$) over $\mathbb{C}$, together with a positive ramification index, invariance of $\mathrm{pt}$ under the group, the characterisation that $x$ lies in the valuation ring of $\mathrm{pt}(\tau)$ exactly when $z \mapsto \|\mathrm{realizeOf}\,\Gamma\,x\,z\|$ is bounded on a punctured neighbourhood of $\tau$, and the stated formula for the meromorphic order of the realisation at $\tau$. Let $\iota : \mathbb{C}\!\cdot\!F_0 \to \mathbb{C}\!\cdot\!F_0'$ be a $\mathbb{C}$-algebra homomorphism which is the identity on the underlying Laurent series, and assume $\iota$ is integral. Then for every $\tau$ the valuation ring of $D'.\mathrm{pt}(\tau)$ pulls back along $\iota$ to that of $D.\mathrm{pt}(\tau)$, i.e. $(D'.\mathrm{pt}(\tau)).\mathrm{restrictAlong}\,\iota = D.\mathrm{pt}(\tau)$.
--
--   This is the statement that the morphism of curves induced by the inclusion of $q$-expansion function fields of level $\Gamma$ into level $\Gamma'$ sends the point of $X(\Gamma')$ determined by $\tau$ to the point of $X(\Gamma)$ determined by $\tau$, in the language of places and their restriction along an integral algebra map. It is used in the construction of Hecke divisors on the modular curve, in [`ModularCurve.ComplexPlaceDictionaryOf.heckeDivHBar_single_pt`](thm.html#ModularCurve.ComplexPlaceDictionaryOf.heckeDivHBar_single_pt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_eq_pt_of_le.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.ComplexPlaceDictionaryOf.restrictAlong_pt_eq_pt_of_le
    {Γ Γ' : Subgroup SL(2, ℤ)} (hle : Γ' ≤ Γ) (hT : ModularGroup.T ∈ Γ')
    {F₀ F₀' : IntermediateField ℚ (LaurentSeries ℚ)} (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀) (D' : ModularCurve.ComplexPlaceDictionaryOf Γ' F₀')
    (ι : ↥(ModularCurve.laurentBaseChange ℂ F₀) →ₐ[ℂ] ↥(ModularCurve.laurentBaseChange ℂ F₀'))
    (hι : ∀ x : ModularCurve.laurentBaseChange ℂ F₀,
      ((ι x : ModularCurve.laurentBaseChange ℂ F₀') : LaurentSeries ℂ) = (x : LaurentSeries ℂ))
    (hint : ι.toRingHom.IsIntegral) (τ : UpperHalfPlane) :
    (D'.pt τ).restrictAlong ι hint = D.pt τ := by sorry
