-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf
-- name    : ModularCurve.ComplexPlaceDictionaryOf.exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/12ef9ea5-65e7-571b-a00a-a18cbc3ae171
-- title:
--   Divisor-level Hecke compatibility of the Abel–Jacobi map for X_H(M)
-- statement:
--   Fix $M \ge 1$ and a subgroup $H \le (\mathbb{Z}/M)^\times$, and write $\Gamma = \Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$ obtained by pulling $H$ back along the lower-right-entry character of $\Gamma_0(M)$. Let $D$ be a complex place dictionary for $\Gamma$ and the $q$-expansion function field $F =$ [`ModularCurve.xHFunctionField M H`](def/ModularCurve_XH.html#L79) $\subseteq \mathbb{Q}((q))$: a map $\mathrm{pt} : \mathfrak{H} \to \mathrm{Place}\,\mathbb{C}(\mathbb{C}F)$ together with positive ramification indices, invariance $\mathrm{pt}(\gamma\tau) = \mathrm{pt}(\tau)$ for $\gamma \in \Gamma$, the description of the valuation subring at $\mathrm{pt}(\tau)$ as those $x$ whose realisation is bounded near $\tau$, and the identity $\mathrm{ord}_\tau(\text{realisation of } x) = e_\tau \cdot \mathrm{ord}_{\mathrm{pt}(\tau)}(x)$. Let $\ell \ge 1$ be prime, assume $y \mapsto y(q^\ell)$ carries $F$ into the function field of $\Gamma \cap \Gamma_0(M\ell)$, assume the two ring maps $\alpha, \beta$ (`heckeAlphaHBar`, `heckeBetaHBar`) over $\mathbb{C}$ are integral, and assume every nonzero element of $\mathbb{C}F'$, $F' =$ `xHTopFunctionFieldC ℚ M H (M*ℓ)`, has a degree-zero divisor recording its orders at all places. Let $c : \mathfrak{H} \to_{\mathrm{f}} \mathbb{Z}$ be finitely supported with $\deg \sum_\tau c(\tau)\,\mathrm{pt}(\tau) = 0$. Then there is a finitely supported $c' : \mathfrak{H} \to_{\mathrm{f}} \mathbb{Z}$ with $\sum_\tau c'(\tau)\,\mathrm{pt}(\tau) = \alpha_*\beta^*\bigl(\sum_\tau c(\tau)\,\mathrm{pt}(\tau)\bigr)$, the correspondence `heckeDivHBar`, such that moreover the functional $\sum_\tau c'(\tau)\,\omega_{i,\tau}$ on $S_2(\Gamma) =$ `CuspForm Γ 2`, where $\omega_{i,\tau}$ is the period functional `periodAlongOf` integrating along the path from $i$ to $\tau$, differs from the transpose of [`CuspForm.heckeTLinH 2`](def/CuspForm_HeckeOperatorFormsGammaH.html#L224) at $\ell$ (whenever $\ell \nmid M$), respectively of [`CuspForm.heckeULinH 2 ℓ`](def/CuspForm_HeckeOperatorFormsGammaH.html#L171) (whenever $\ell \mid M$), applied to $\sum_\tau c(\tau)\,\omega_{i,\tau}$, by an element of the period lattice `periodLatticeOf Γ`, the $\mathbb{Z}$-span of the periods of $\Gamma$.
--
--   This is the Eichler–Shimura compatibility at the level of divisors: under the Abel–Jacobi map given by integration of weight-two cusp forms along paths from $i$, the Hecke correspondence $\alpha_*\beta^*$ on divisors of $X_H(M)_{\mathbb{C}}$ induces, modulo periods, the transpose of $T_\ell$ for $\ell \nmid M$ and of $U_\ell$ for $\ell \mid M$. It feeds the construction of the Hecke-equivariant isomorphism between $\mathrm{Pic}^0$ of $X_H(M)_{\mathbb{C}}$ and the dual of $S_2(\Gamma_H(M))$ modulo the period lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.ComplexPlaceDictionaryOf.exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (h0 : ModularCurve.HeckeBetaHDefined M H ℓ)
    (hα : ModularCurve.HeckeAlphaHBarIntegral ℂ M H ℓ) (hβ : ModularCurve.HeckeBetaHBarIntegral ℂ M H ℓ)
    [AlgebraicCurve.HasPrincipalDivisors ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))]
    (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0) :
    ∃ c' : UpperHalfPlane →₀ ℤ,
      Finsupp.mapDomain D.pt c' = ModularCurve.heckeDivHBar hα hβ (Finsupp.mapDomain D.pt c) ∧
      (∀ hℓM : ¬ ℓ ∣ M,
        (c'.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) -
            (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap
              (c.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) ∈
          ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) ∧
      (ℓ ∣ M →
        (c'.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) -
            (CuspForm.heckeULinH 2 ℓ).dualMap
              (c.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) ∈
          ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) := by sorry
