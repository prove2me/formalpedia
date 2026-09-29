-- Prove2me | Theorems.Thm_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup
-- name    : ModularCurve.exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/b5784056-68fe-53ae-9125-8f492a72852b
-- title:
--   Integral parabolic characters as the ℤ-dual of the period lattice
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ satisfying the predicate `CongruenceSubgroup.IsCongruenceSubgroup`. Write $\mathrm{parabolicHoms}\ \mathbb{Z}\ \Gamma\ \mathbb{Z}$ for the $\mathbb{Z}$-submodule of additive homomorphisms $\psi \colon \mathrm{Additive}\ \Gamma \to \mathbb{Z}$ that vanish on every $\gamma \in \Gamma$ whose underlying integral $2 \times 2$ matrix satisfies $\mathrm{tr}(\gamma)^2 = 4$, and let $\mathrm{periodLatticeOf}\ \Gamma \subseteq \mathrm{Hom}_{\mathbb{C}}(\mathrm{CuspForm}\ \Gamma\ 2, \mathbb{C})$ be the $\mathbb{Z}$-span of the functionals $\mathrm{periodOf}\ \Gamma\ \gamma$, $\gamma \in \Gamma$, where $\mathrm{periodOf}\ \Gamma\ \gamma$ is the linear functional obtained by integrating the period integrand along the parametrised path from $i$ to $\gamma \cdot i$ in the upper half plane, i.e. $f \mapsto \int_i^{\gamma i} f$. The assertion is that there exists a $\mathbb{Z}$-linear isomorphism $$EV \colon \mathrm{parabolicHoms}\ \mathbb{Z}\ \Gamma\ \mathbb{Z} \xrightarrow{\ \sim\ } \mathrm{Hom}_{\mathbb{Z}}(\mathrm{periodLatticeOf}\ \Gamma, \mathbb{Z})$$ such that for every parabolic homomorphism $\psi$ and every $\delta \in \Gamma$, the value of $EV\,\psi$ at the lattice element $\mathrm{periodOf}\ \Gamma\ \delta$ equals $\psi(\mathrm{Additive.ofMul}\ \delta)$. Thus evaluation on periods identifies integral parabolic characters of $\Gamma$ with the $\mathbb{Z}$-dual of the period lattice.
--
--   This is the integral form of Eichler–Shimura duality $H^1_{\mathrm{par}}(\Gamma,\mathbb{Z}) \cong \mathrm{Hom}_{\mathbb{Z}}(H_1(X_\Gamma,\mathbb{Z}),\mathbb{Z})$, presented concretely in terms of period functionals on weight-two cusp forms. It feeds the comparison of the module of integral parabolic characters with the dual of the Tate module of the Jacobian $J_H$, used in [`ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH`](thm.html#ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH) and its variant involving the character involution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup
    (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) :
    ∃ EV : ModularCurve.Period.parabolicHoms ℤ Γ ℤ ≃ₗ[ℤ] Module.Dual ℤ (ModularCurve.periodLatticeOf Γ),
      ∀ (ψ : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) (δ : Γ),
        EV ψ ⟨ModularCurve.periodOf Γ δ, ModularCurve.periodOf_mem_periodLatticeOf Γ δ⟩ =
          (ψ : Additive Γ →+ ℤ) (Additive.ofMul δ) := by sorry
