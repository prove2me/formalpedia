-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH
-- name    : ModularCurve.ComplexPlaceDictionaryOf.isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/fc163634-c863-5029-871d-8229f29ab87c
-- title:
--   Abel's theorem for X_H(M): sufficiency
-- statement:
--   Fix $M \ge 1$ (nonzero) and a subgroup $H \le (\mathbb{Z}/M)^\times$, and let $\Gamma_H(M)$ be the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the character $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$ given by the lower-right entry mod $M$. Let $F_0 =$ [`ModularCurve.xHFunctionField M H`](def/ModularCurve_XH.html#L79) be the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the $q$-expansion ratios attached to $\Gamma_H(M)$, and let $D$ be a complex place dictionary for $(\Gamma_H(M), F_0)$: a map $\mathrm{pt}$ from $\mathfrak{H}$ to the places of the coefficient base change $\mathbb{C}F_0$ over $\mathbb{C}$, together with positive ramification indices, $\Gamma_H(M)$-invariance of $\mathrm{pt}$, the characterisation of the valuation subring of $\mathrm{pt}(\tau)$ by local boundedness near $\tau$ of the realisation `realizeOf`, and the identity $\mathrm{ord}_{\tau}$ of the realisation $=$ (ramification at $\tau$) $\cdot\ \mathrm{ord}_{\mathrm{pt}(\tau)}$ for nonzero elements. Let $c : \mathfrak{H} \to \mathbb{Z}$ be finitely supported and assume: the divisor $\sum_\tau c(\tau)\,\mathrm{pt}(\tau)$ obtained by pushing $c$ forward along $\mathrm{pt}$ has degree $0$; and the functional $f \mapsto \sum_\tau c(\tau)\int_i^{\tau} f(z)\,dz$ on $S_2(\Gamma_H(M))$, defined as the $\mathbb{Z}$-combination of the straight-line period functionals `periodAlongOf` from $i$ to $\tau$, lies in the period lattice `periodLatticeOf`, the $\mathbb{Z}$-span of the functionals $f \mapsto \int_i^{\gamma i} f(z)\,dz$ for $\gamma \in \Gamma_H(M)$. Then that divisor is principal: there is a nonzero $x \in \mathbb{C}F_0$ with $\mathrm{ord}_v(x)$ equal to the divisor's coefficient at $v$ for every place $v$ of $\mathbb{C}F_0$ over $\mathbb{C}$.
--
--   This is the sufficiency half of Abel's theorem for the modular curve $X_H(M)$, equivalently the injectivity statement underlying the Abel–Jacobi description of $\mathrm{Pic}^0$: a degree-zero divisor supported at points of $\mathfrak{H}$ whose Abel–Jacobi image is a period of $\Gamma_H(M)$ is the divisor of a function in the function field. It is used in the construction of the bijective Hecke-equivariant maps from $\mathrm{Pic}^0$ of the complex curve $X_H(M)$ to the quotient of $S_2(\Gamma_H(M))^\vee$ by the period lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.ComplexPlaceDictionaryOf.isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0)
    (hΛ : (c.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) ∈
      ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :
    AlgebraicCurve.Divisor.IsPrincipal (Finsupp.mapDomain D.pt c) := by sorry
