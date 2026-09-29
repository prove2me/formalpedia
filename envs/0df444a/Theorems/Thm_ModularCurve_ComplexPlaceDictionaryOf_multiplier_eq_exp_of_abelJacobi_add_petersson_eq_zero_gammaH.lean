-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_multiplier_eq_exp_of_abelJacobi_add_petersson_eq_zero_gammaH
-- name    : ModularCurve.ComplexPlaceDictionaryOf.multiplier_eq_exp_of_abelJacobi_add_petersson_eq_zero_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/8529e762-cd90-5771-a317-3eef2afd4a79
-- title:
--   Unitary multiplier as exponential of a period on X_H(M)
-- statement:
--   Fix $M\ge 1$ and a subgroup $H\le(\mathbb{Z}/M)^{\times}$, and write $\Gamma=$ [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) for the subgroup of $SL(2,\mathbb{Z})$ obtained as the image under the inclusion $\Gamma_0(M)\hookrightarrow SL(2,\mathbb{Z})$ of the preimage of $H$ under the lower-right-entry character $\Gamma_0(M)\to(\mathbb{Z}/M)^{\times}$. Let $D$ be a complex place dictionary for $\Gamma$ and the $q$-expansion function field [`ModularCurve.xHFunctionField M H`](def/ModularCurve_XH.html#L79), i.e. a map $\mathrm{pt}$ from $\mathfrak{H}$ to the places of the base-changed function field over $\mathbb{C}$ together with positive ramification indices $e_\tau$, such that $\mathrm{pt}$ is $\Gamma$-invariant, membership of $x$ in the valuation subring at $\mathrm{pt}(\tau)$ is equivalent to local boundedness near $\tau$ of the norm of the realisation of $x$ as a function on $\mathfrak{H}$, and $\mathrm{ord}_{\tau}$ of that realisation equals $e_\tau\cdot\mathrm{ord}_{\mathrm{pt}(\tau)}(x)$ for $x\neq 0$. Let $c:\mathfrak{H}\to\mathbb{Z}$ be finitely supported whose pushforward divisor $\tilde c=\mathrm{mapDomain}\,\mathrm{pt}\,c$ has degree zero (the sum of its coefficients weighted by the place degrees). Let $F:\mathfrak{H}\to\mathbb{C}$, $\chi:\Gamma\to\mathbb{C}$ and $f$ a weight-$2$ cusp form on $\Gamma$, subject to: $F$ is meromorphic at every point of $\mathfrak{H}$ (after transport along `ofComplex`); $F(\gamma\tau)=\chi(\gamma)F(\tau)$ for all $\gamma\in\Gamma$, $\tau\in\mathfrak{H}$; $\lvert\chi(\gamma)\rvert=1$; for each $\sigma\in SL(2,\mathbb{Z})$ the function $\tau\mapsto F(\sigma\tau)$ tends to a nonzero limit as $\operatorname{Im}\tau\to\infty$; and the meromorphic order of $F$ at each $\tau$ equals $e_\tau\cdot\tilde c(\mathrm{pt}(\tau))$. Assume finally that for every weight-$2$ cusp form $g$ on $\Gamma$ the value at $g$ of the functional $\sum_{\tau}c(\tau)\cdot$ (integration along the segment from $i$ to $\tau$) plus $i$ times the integral of the pointwise weight-$2$ Petersson product of $f$ and $g$ over the fundamental set [`FLT.Gamma0FundamentalSet.gammaFundamentalSet`](def/AutomorphicForm_Gamma0FundamentalSet.html#L13) of $\Gamma\vee\langle-1\rangle$ vanishes. Then for every $\gamma\in\Gamma$, $\chi(\gamma)=\exp\bigl(2\pi i\,\operatorname{Re}\int_{i}^{\gamma i}f\bigr)$, the period being [`ModularCurve.periodOf`](def/ModularCurve_PeriodOf.html#L56), the integral of $f$ along the segment from $i$ to $\gamma\cdot i$.
--
--   This is the reciprocity law relating the differential of the third kind $d\log F$, with residue divisor $\tilde c$ and unitary multiplier system $\chi$, to the holomorphic differentials on the modular curve $X_H(M)$: it identifies $\chi$ on $\Gamma_H(M)$ with the exponential of the real parts of the periods of the cusp form $f$ whose Petersson functional cancels the Abel–Jacobi functional of $\tilde c$. It is the level-$\Gamma_H(M)$ form of the sufficiency direction of Abel's theorem used in the construction of functions with prescribed divisor, and feeds into [`ModularCurve.ComplexPlaceDictionaryOf.exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLatticeOf_gammaH`](thm.html#ModularCurve.ComplexPlaceDictionaryOf.exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLatticeOf_gammaH).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_multiplier_eq_exp_of_abelJacobi_add_petersson_eq_zero_gammaH.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology

theorem ModularCurve.ComplexPlaceDictionaryOf.multiplier_eq_exp_of_abelJacobi_add_petersson_eq_zero_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0)
    (F : ℍ → ℂ) (χ : CohCarrier.GammaH M H → ℂ)
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CohCarrier.GammaH M H) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hunit : ∀ γ : CohCarrier.GammaH M H, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) : ℤ) : WithTop ℤ))
    (hf : ∀ g : CuspForm (CohCarrier.GammaH M H) 2,
      (c.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) g +
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))), UpperHalfPlane.petersson 2 ⇑f ⇑g τ) = 0) :
    ∀ γ : CohCarrier.GammaH M H,
      χ γ = Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf (CohCarrier.GammaH M H) γ f).re : ℂ)) := by sorry
