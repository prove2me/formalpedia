-- Prove2me | Theorems.Thm_ModularCurve_exists_isParabolicHom_apply_eq_period
-- name    : ModularCurve.exists_isParabolicHom_apply_eq_period
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/84b98f60-712d-5902-9caf-057c94bcec1f
-- title:
--   The period map is a parabolic homomorphism on Γ₀(N)
-- statement:
--   Let $N$ be a natural number, assumed nonzero. The assertion is the existence of an additive homomorphism $\Phi$ from the additive copy `Additive (CongruenceSubgroup.Gamma0 N)` of the group $\Gamma_0(N)$ to the $\mathbb{C}$-linear dual `Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)` of the space of weight-$2$ cusp forms for $\Gamma_0(N)$, with two properties. First, $\Phi$ satisfies [`ModularCurve.Period.IsParabolicHom`](def/ModularCurve_PeriodMap.html#L15) for $\Gamma_0(N)$: for every $\gamma \in \Gamma_0(N)$ whose underlying integer matrix has $\operatorname{tr}(\gamma)^2 = 4$, the functional $\Phi(\gamma)$ is zero. Second, $\Phi$ computes the period functionals: for every $\gamma \in \Gamma_0(N)$ one has $\Phi(\mathrm{ofMul}\,\gamma) =$ [`ModularCurve.period N γ`](def/ModularCurve_PeriodLattice.html#L92), the element of the dual given by `periodAlong N UpperHalfPlane.I ((γ : SL(2, ℤ)) • UpperHalfPlane.I)`, i.e. the functional sending a cusp form $f$ to the interval integral over $t \in [0,1]$ of the integrand `periodIntegrand N UpperHalfPlane.I ((γ : SL(2, ℤ)) • UpperHalfPlane.I) f` parametrising the path from $i$ to $\gamma \cdot i$ in the upper half-plane. In particular the map $\gamma \mapsto$ [`ModularCurve.period N γ`](def/ModularCurve_PeriodLattice.html#L92) is itself additive in $\gamma$ (written multiplicatively in $\Gamma_0(N)$) and vanishes on elements of trace $\pm 2$.
--
--   This is the Eichler–Shimura–Manin period map $\gamma \mapsto \int_i^{\gamma i}(\cdot)$, packaged as a homomorphism $\Gamma_0(N) \to S_2(\Gamma_0(N))^{\vee}$ that kills parabolic elements, so that its image is the period lattice of the modular curve. It is used downstream in the construction of the Abel–Jacobi and Petersson-type statements about the period lattice and about multipliers of norm one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isParabolicHom_apply_eq_period.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_isParabolicHom_apply_eq_period (N : ℕ) [NeZero N] :
    ∃ Φ : Additive (CongruenceSubgroup.Gamma0 N) →+
        Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2),
      ModularCurve.Period.IsParabolicHom (CongruenceSubgroup.Gamma0 N) Φ ∧
        ∀ γ : CongruenceSubgroup.Gamma0 N, Φ (Additive.ofMul γ) = ModularCurve.period N γ := by sorry
