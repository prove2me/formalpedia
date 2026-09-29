-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_realizeOf_mul_deriv_realizeOf_eq_div_add_gammaH
-- name    : ModularCurve.ComplexPlaceDictionaryOf.exists_realizeOf_mul_deriv_realizeOf_eq_div_add_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/edbda9d3-0ebe-5a4c-a3c4-438b1129a45f
-- title:
--   Polar part at τ of a realised differential a dx
-- statement:
--   Fix $M\ge 1$ and a subgroup $H\le(\mathbb{Z}/M)^{\times}$, write $\Gamma=\mathrm{GammaH}\,M\,H$ for the congruence subgroup of $SL(2,\mathbb{Z})$ obtained by pulling $H$ back along the determinant-type character `gamma0Units` of $\Gamma_0(M)$, and let $E=$ `laurentBaseChange ℂ (xHFunctionField M H)` be the subfield of $\mathbb{C}((q))$ generated over $\mathbb{C}$ by the coefficientwise image of the rational $q$-expansion function field of $\Gamma$. Let $D$ be a complex place dictionary for this pair: a map $\mathrm{pt}:\mathfrak{H}\to$ places of $E/\mathbb{C}$ (valuation subrings containing $\mathbb{C}$, proper, principal) together with positive integers $e_\tau=D.\mathrm{ramification}(\tau)$, invariant under $\Gamma$, such that membership in the valuation subring of $\mathrm{pt}(\tau)$ is equivalent to local boundedness near $\tau$ of the $\Gamma$-realisation `realizeOf`, and such that the meromorphic order at $\tau$ of the realisation of $x\neq 0$ equals $e_\tau\cdot\mathrm{ord}_{\mathrm{pt}(\tau)}x$. Assume at every place $w$ of $E/\mathbb{C}$ that $d$ of the distinguished uniformizer spans $\Omega_{E/\mathbb{C}}$. Let $a,x,\pi\in E$, $\tau\in\mathfrak{H}$, $v=\mathrm{pt}(\tau)$, and $\eta\in\Omega_{E/\mathbb{C}}$ with $\eta=a\,dx$, $\eta\neq 0$, $\mathrm{ord}_v$ of the coefficient $c$ of $\eta$ against $v.\mathrm{dCoord}$ at least $-1$, $\mathrm{ord}_v\pi=1$ and $v.\mathrm{dCoord}=d\pi$. Then there exist $\rho\in\mathbb{C}$ and $g:\mathbb{C}\to\mathbb{C}$ such that $c\pi-\rho$ lies in the nonunits of the valuation subring of $v$, $\rho\neq 0$ if and only if $\mathrm{ord}_v c=-1$, $g$ is analytic at $\tau$, and for $z$ in a punctured neighbourhood of $\tau$ in $\mathbb{C}$ one has $\widetilde{a}(z)\cdot\frac{d}{dz}\widetilde{x}(z)=e_\tau\rho/(z-\tau)+g(z)$, where $\widetilde{y}$ denotes $z\mapsto$ `realizeOf` $\Gamma$ $y$ $(\mathrm{ofComplex}\,z)$.
--
--   This compares the algebraic residue of a differential $\eta=a\,dx$ of the function field of $X_H(M)$ at the place below $\tau$ with the analytic polar part at $\tau$ of the associated weight-two meromorphic function $\widetilde{a}\cdot\widetilde{x}'$ on the upper half plane, the discrepancy being the ramification index $e_\tau$ of $\mathfrak{H}\to X_H(M)$. It is used in the construction of a slash-invariant object with non-vanishing residue at a prescribed point, [`ModularCurve.ComplexPlaceDictionaryOf.exists_slashInvariant_residue_ne_zero_of_pt_ne_gammaH`](thm.html#ModularCurve.ComplexPlaceDictionaryOf.exists_slashInvariant_residue_ne_zero_of_pt_ne_gammaH).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_realizeOf_mul_deriv_realizeOf_eq_div_add_gammaH.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.ComplexPlaceDictionaryOf.exists_realizeOf_mul_deriv_realizeOf_eq_div_add_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    [∀ w : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)), w.DCoordGenerates]
    (a x π : ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) (τ : ℍ)
    (η : Ω[(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))⁄ℂ])
    (hηax : η = a • KaehlerDifferential.D ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) x)
    (hη : η ≠ 0) (hord : -1 ≤ (D.pt τ).ordDifferential η)
    (hπ : (D.pt τ).ord π = 1)
    (hdπ : (D.pt τ).dCoord = KaehlerDifferential.D ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) π) :
    ∃ (ρ : ℂ) (g : ℂ → ℂ),
      (D.pt τ).differentialCoeff η * π - algebraMap ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) ρ ∈
        (D.pt τ).toValuationSubring.nonunits ∧
      (ρ ≠ 0 ↔ (D.pt τ).ordDifferential η = -1) ∧
      AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ),
        ModularCurve.realizeOf (CohCarrier.GammaH M H) (a : LaurentSeries ℂ) (ofComplex z) *
            deriv (fun w : ℂ => ModularCurve.realizeOf (CohCarrier.GammaH M H) (x : LaurentSeries ℂ) (ofComplex w)) z =
          (D.ramification τ : ℂ) * ρ / (z - τ) + g z := by sorry
