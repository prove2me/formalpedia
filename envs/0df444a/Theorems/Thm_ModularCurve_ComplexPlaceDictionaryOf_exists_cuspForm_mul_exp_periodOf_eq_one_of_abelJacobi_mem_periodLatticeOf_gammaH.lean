-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_cuspForm_mul_exp_periodOf_eq_one_of_abelJacobi_mem_periodLatticeOf_gammaH
-- name    : ModularCurve.ComplexPlaceDictionaryOf.exists_cuspForm_mul_exp_periodOf_eq_one_of_abelJacobi_mem_periodLatticeOf_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/d6ab1621-5033-51a0-b203-edc446dc547a
-- title:
--   Abel's theorem for X_H(M): multiplier is a period exponential
-- statement:
--   Fix $M \ge 1$ and a subgroup $H \le (\mathbb{Z}/M)^\times$, and let $\Gamma = \Gamma_H(M)$ be the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $SL(2,\mathbb{Z})$, the image in $SL(2,\mathbb{Z})$ of the matrices of $\Gamma_0(M)$ whose diagonal character under `gamma0Units` lies in $H$. Let $D$ be a complex place dictionary for $\Gamma$ and the $q$-expansion function field [`ModularCurve.xHFunctionField M H`](def/ModularCurve_XH.html#L79): thus $D$ provides a map $\mathrm{pt}$ from the upper half-plane $\mathfrak{H}$ to the places of the base-changed field over $\mathbb{C}$, positive ramification indices $e_\tau$, invariance $\mathrm{pt}(\gamma\tau) = \mathrm{pt}(\tau)$ for $\gamma \in \Gamma$, the description of the valuation subring at $\mathrm{pt}(\tau)$ as the elements whose realisations are locally bounded near $\tau$ on punctured neighbourhoods, and the identity $\mathrm{ord}_\tau(\text{realisation of } x) = e_\tau \cdot \mathrm{ord}_{\mathrm{pt}(\tau)}(x)$ for $x \ne 0$. Let $c : \mathfrak{H} \to \mathbb{Z}$ be finitely supported, and write $\tilde c$ for its pushforward along $\mathrm{pt}$, a divisor; assume $\deg \tilde c = 0$ (the sum of the coefficients weighted by the local degrees of the places) and that the functional $f \mapsto \sum_\tau c(\tau)\int_i^{\tau} f$, where each integral is taken along the straight segment from $i$ to $\tau$, lies in the period lattice $\Lambda_\Gamma \subseteq S_2(\Gamma)^\vee$, the $\mathbb{Z}$-span of the functionals $f \mapsto \int_i^{\gamma i} f$ for $\gamma \in \Gamma$. Let $F : \mathfrak{H} \to \mathbb{C}$ and $\chi : \Gamma \to \mathbb{C}$ satisfy: $z \mapsto F(z)$ is meromorphic at every point of $\mathfrak{H}$; $F(\gamma\tau) = \chi(\gamma) F(\tau)$ for all $\gamma \in \Gamma$ and $\tau$; for every $\sigma \in SL(2,\mathbb{Z})$ the function $\tau \mapsto F(\sigma\tau)$ tends to a nonzero limit as $\operatorname{Im}\tau \to \infty$; and $\mathrm{ord}_\tau F = e_\tau \cdot \tilde c(\mathrm{pt}(\tau))$ for every $\tau \in \mathfrak{H}$. Then there is a cusp form $f$ of weight $2$ on $\Gamma$ such that $\chi(\gamma)\exp\bigl(\int_i^{\gamma i} f\bigr) = 1$ for every $\gamma \in \Gamma$. No unitarity of $\chi$ is assumed.
--
--   This is the multiplier computation at the heart of the sufficiency direction of Abel's theorem on the complex modular curve $X_H(M)$: a multiplicative function with divisor $\tilde c$ and nonzero limits at all cusps has multiplier equal to the inverse of a cusp-form period exponential, once the Abel–Jacobi sum of $\tilde c$ is a period. It feeds the construction of a meromorphic function on $X_H(M)(\mathbb{C})$ with prescribed divisor, via [`ModularCurve.ComplexPlaceDictionaryOf.exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH`](thm.html#ModularCurve.ComplexPlaceDictionaryOf.exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_cuspForm_mul_exp_periodOf_eq_one_of_abelJacobi_mem_periodLatticeOf_gammaH.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Topology

theorem ModularCurve.ComplexPlaceDictionaryOf.exists_cuspForm_mul_exp_periodOf_eq_one_of_abelJacobi_mem_periodLatticeOf_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0)
    (hΛ : (c.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) ∈
      ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (F : UpperHalfPlane → ℂ) (χ : CohCarrier.GammaH M H → ℂ)
    (hF : ∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CohCarrier.GammaH M H) (τ : UpperHalfPlane), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : UpperHalfPlane => F (σ • τ)) UpperHalfPlane.atImInfty (𝓝 L))
    (hord : ∀ τ : UpperHalfPlane, meromorphicOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) (τ : ℂ) =
      (((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) : ℤ) : WithTop ℤ)) :
    ∃ f : CuspForm (CohCarrier.GammaH M H) 2,
      ∀ γ : CohCarrier.GammaH M H,
        χ γ * Complex.exp (ModularCurve.periodOf (CohCarrier.GammaH M H) γ f) = 1 := by sorry
