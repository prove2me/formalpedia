-- Prove2me | Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_comp_of_coe_eq_slash
-- name    : ModularCurve.periodMapOf_gammaH_eq_comp_of_coe_eq_slash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/c4c55e2b-5918-57ea-acbd-5b529aa1ab16
-- title:
--   Periods intertwine slashing by α with conjugation by α
-- statement:
--   Let $M$ be a positive natural number, $H$ a subgroup of $(\mathbb Z/M)^\times$, and let $\Gamma =$ [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) be the subgroup of $\mathrm{SL}_2(\mathbb Z)$ consisting of the matrices of $\Gamma_0(M)$ whose lower-right entry, viewed as a unit of $\mathbb Z/M$, lies in $H$. Let $\alpha \in \mathrm{GL}_2(\mathbb R)$ have positive determinant, and let $c \colon \Gamma \to \Gamma$ be a monoid homomorphism such that for every $\delta \in \Gamma$ the image of $c\,\delta$ in $\mathrm{GL}_2(\mathbb R)$ equals $\alpha \delta \alpha^{-1}$; thus $\alpha$ normalises $\Gamma$ and $c$ is the induced conjugation, supplied as data so that no normaliser computation enters the statement. Let $f, g$ be cusp forms of weight $2$ on $\Gamma$ whose underlying functions satisfy $g = f \mid_{2} \alpha$. The conclusion is an equality of additive homomorphisms $\mathrm{Additive}\,\Gamma \to \mathbb C$: the period map [`ModularCurve.periodMapOf`](def/ModularCurve_PeriodOf.html#L79) of $g$ (the period homomorphism attached to a choice of equivariant primitive of $g$ tending to $0$ at the cusps, and $0$ if no such primitive exists) equals the period map of $f$ precomposed with the additive homomorphism induced by $c$, i.e. $\operatorname{per}(g)(\delta) = \operatorname{per}(f)(\alpha\delta\alpha^{-1})$ for all $\delta \in \Gamma$.
--
--   This is the compatibility of the weight-two period character with the slash action of a determinant-positive element of $\mathrm{GL}_2(\mathbb R)$ normalising $\Gamma_H(M)$, conjugation on $\Gamma$ corresponding to slashing on cusp forms. It is the general form behind the diamond operators and the degeneracy/Atkin–Lehner type maps, and is used in the construction of the linear maps from cusp forms into the cohomology and Tate-module comparisons at level $\Gamma_H(M)$ and full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodMapOf_gammaH_eq_comp_of_coe_eq_slash.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm TensorProduct

theorem ModularCurve.periodMapOf_gammaH_eq_comp_of_coe_eq_slash
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (α : GL (Fin 2) ℝ)
    (hα : 0 < ((Matrix.GeneralLinearGroup.det α : ℝˣ) : ℝ))
    (c : ↥(CohCarrier.GammaH M H) →* ↥(CohCarrier.GammaH M H))
    (hc : ∀ δ : ↥(CohCarrier.GammaH M H),
      (((c δ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) = α * ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) * α⁻¹)
    (f g : CuspForm (CohCarrier.GammaH M H) 2) (hg : ⇑g = ⇑f ∣[(2 : ℤ)] α) :
    ModularCurve.periodMapOf (CohCarrier.GammaH M H) g =
      (ModularCurve.periodMapOf (CohCarrier.GammaH M H) f).comp (MonoidHom.toAdditive c) := by sorry
