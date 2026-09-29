-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_multiplier_eq_one_of_norm_eq_one_of_abelJacobi_mem_periodLatticeOf_gammaH
-- name    : ModularCurve.ComplexPlaceDictionaryOf.multiplier_eq_one_of_norm_eq_one_of_abelJacobi_mem_periodLatticeOf_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/86e3510a-4689-5171-899f-221e64de1606
-- title:
--   Unitary multiplier is trivial when Abel–Jacobi class is a period
-- statement:
--   Fix $M \ge 1$ and a subgroup $H \le (\mathbb{Z}/M)^\times$, and let $\Gamma = \Gamma_H(M)$ be the subgroup of $SL(2,\mathbb{Z})$ obtained by pushing forward, along the inclusion of $\Gamma_0(M)$, the preimage of $H$ under the homomorphism $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$ sending $\gamma$ to its lower-right entry mod $M$. Let $D$ be a complex place dictionary for $\Gamma$ and the function field [`ModularCurve.xHFunctionField M H`](def/ModularCurve_XH.html#L79), that is: a map $\mathrm{pt}$ from $\mathfrak{H}$ to the places of the base change to $\mathbb{C}$ of that field, a positive integer-valued ramification function $e$ on $\mathfrak{H}$, $\Gamma$-invariance of $\mathrm{pt}$, the description of the valuation subring of $\mathrm{pt}(\tau)$ as the set of elements whose realisation as a function on $\mathfrak{H}$ is bounded in norm near $\tau$ on the punctured neighbourhood filter, and the identity $\mathrm{ord}_\tau(\mathrm{realize}\,x) = e(\tau)\cdot \mathrm{ord}_{\mathrm{pt}(\tau)}(x)$ for $x \ne 0$. Let $c : \mathfrak{H} \to \mathbb{Z}$ be finitely supported such that the pushforward divisor $\mathrm{pt}_*c$ has degree $0$ (degree being the sum of the coefficients weighted by the residue degrees of the places), and such that the functional $f \mapsto \sum_\tau c(\tau)\int_i^\tau f$ on weight-two cusp forms for $\Gamma$, where the integral is taken along the straight segment from $i$ to $\tau$, lies in the period lattice of $\Gamma$, the $\mathbb{Z}$-span of the functionals $f \mapsto \int_i^{\gamma i} f$ for $\gamma \in \Gamma$. Let $F : \mathfrak{H} \to \mathbb{C}$ and $\chi : \Gamma \to \mathbb{C}$ satisfy: $F$ is meromorphic at every point of $\mathfrak{H}$; $F(\gamma\tau) = \chi(\gamma)F(\tau)$ for all $\gamma \in \Gamma$ and $\tau$; $\|\chi(\gamma)\| = 1$ for all $\gamma$; for every $\sigma \in SL(2,\mathbb{Z})$ the function $\tau \mapsto F(\sigma\tau)$ tends to a nonzero limit as $\operatorname{Im}\tau \to \infty$; and $\mathrm{ord}_\tau F = e(\tau)\cdot(\mathrm{pt}_*c)(\mathrm{pt}(\tau))$ for every $\tau$. Then $\chi(\gamma) = 1$ for every $\gamma \in \Gamma$.
--
--   This is the step in the sufficiency half of Abel's theorem for the modular curve $X_H(M)$ which rules out a nontrivial unitary multiplier system: once the Abel–Jacobi sum of a degree-zero divisor is a period, any multiplicative meromorphic function realising that divisor with unitary multiplier is genuinely $\Gamma_H(M)$-invariant. It is used in the construction of a weight-two cusp form whose exponentiated periods are all trivial, and hence in the passage from the period lattice to the divisor class group of $X_H(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_multiplier_eq_one_of_norm_eq_one_of_abelJacobi_mem_periodLatticeOf_gammaH.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Topology

theorem ModularCurve.ComplexPlaceDictionaryOf.multiplier_eq_one_of_norm_eq_one_of_abelJacobi_mem_periodLatticeOf_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0)
    (hΛ : (c.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) ∈
      ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (F : UpperHalfPlane → ℂ) (χ : CohCarrier.GammaH M H → ℂ)
    (hF : ∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CohCarrier.GammaH M H) (τ : UpperHalfPlane), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hunit : ∀ γ : CohCarrier.GammaH M H, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : UpperHalfPlane => F (σ • τ)) UpperHalfPlane.atImInfty (𝓝 L))
    (hord : ∀ τ : UpperHalfPlane, meromorphicOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) (τ : ℂ) =
      (((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) : ℤ) : WithTop ℤ))
    (γ : CohCarrier.GammaH M H) : χ γ = 1 := by sorry
