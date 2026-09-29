-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH
-- name    : ModularCurve.ComplexPlaceDictionaryOf.exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/b92ded64-2cbb-5543-9641-a52ca8af59e8
-- title:
--   Analytic sufficiency in Abel's theorem for X_H(M)
-- statement:
--   Fix $M \geq 1$ and a subgroup $H \leq (\mathbb{Z}/M)^\times$, and let $\Gamma = \Gamma_H(M)$ be the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained by pulling $H$ back along the character $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$ given by the lower right entry. Let $D$ be a complex place dictionary for $\Gamma$ and the $q$-expansion function field $F_0 =$ [`ModularCurve.xHFunctionField M H`](def/ModularCurve_XH.html#L79) over $\mathbb{Q}$: thus $D$ assigns to each $\tau \in \mathfrak{H}$ a place $D.\mathrm{pt}(\tau)$ of the base change of $F_0$ to $\mathbb{C}$ and an integer $D.\mathrm{ramification}(\tau) \geq 1$, the assignment being constant on $\Gamma$-orbits, with the valuation subring at $\tau$ cut out by local boundedness of the analytic realisation near $\tau$ and with $\mathrm{ord}_\tau$ of the realisation of $x \neq 0$ equal to $D.\mathrm{ramification}(\tau) \cdot \mathrm{ord}_{D.\mathrm{pt}(\tau)}(x)$. Let $c : \mathfrak{H} \to \mathbb{Z}$ be finitely supported and let $\tilde c$ be its pushforward along $D.\mathrm{pt}$, a divisor on the places. Assume $\tilde c$ has degree $0$ (coefficients weighted by the degrees of the places) and that the functional $\sum_\tau c(\tau) \cdot \big(f \mapsto \int_i^\tau f\big)$, the integral being taken along the straight segment from $i$ to $\tau$, lies in the period lattice of $\Gamma$, i.e. the $\mathbb{Z}$-span in $\mathrm{Hom}_\mathbb{C}(S_2(\Gamma), \mathbb{C})$ of the functionals $f \mapsto \int_i^{\gamma i} f$ for $\gamma \in \Gamma$. Then there exists $F : \mathfrak{H} \to \mathbb{C}$ such that $z \mapsto F(z)$ is meromorphic at every point of $\mathfrak{H}$, $F(\gamma \tau) = F(\tau)$ for all $\gamma \in \Gamma$ and all $\tau$, for each $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ the function $\tau \mapsto F(\sigma\tau)$ tends to a nonzero limit as $\mathrm{Im}\,\tau \to \infty$, and $\mathrm{ord}_\tau F = D.\mathrm{ramification}(\tau) \cdot \tilde c(D.\mathrm{pt}(\tau))$ for every $\tau \in \mathfrak{H}$.
--
--   This is the analytic half of the sufficiency direction of Abel's theorem for the modular curve $X_H(M)$: a degree-zero divisor whose Abel–Jacobi image is a period is the divisor of a $\Gamma_H(M)$-invariant meromorphic function on $\mathfrak{H}$ with nonzero limits at all cusps. It is used to prove that such a divisor class is principal in the divisor class group of the function field of $X_H(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Topology

theorem ModularCurve.ComplexPlaceDictionaryOf.exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0)
    (hΛ : (c.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) ∈
      ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :
    ∃ F : UpperHalfPlane → ℂ,
      (∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) (τ : ℂ)) ∧
      (∀ γ ∈ CohCarrier.GammaH M H, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ) ∧
      (∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
        Filter.Tendsto (fun τ : UpperHalfPlane => F (σ • τ)) UpperHalfPlane.atImInfty (𝓝 L)) ∧
      ∀ τ : UpperHalfPlane, meromorphicOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) (τ : ℂ) =
        (((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) : ℤ) : WithTop ℤ) := by sorry
