-- Prove2me | Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp
-- name    : ModularCurve.Period.exists_basis_parabolicHoms_castAddHom_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/63e31f11-3de3-5c5d-846a-f1f14017a610
-- title:
--   An integral basis of parabolic characters survives base change
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}(2,\mathbb{Z})$ of finite index. For a commutative coefficient setup, [`ModularCurve.Period.parabolicHoms R Γ A`](def/ModularCurve_PeriodMap.html#L62) denotes the $R$-submodule of the additive homomorphisms $\mathrm{Additive}\,\Gamma \to A$ consisting of those $\varphi$ that vanish on every $\gamma \in \Gamma$ whose underlying integral matrix has $(\operatorname{tr}\gamma)^2 = 4$, i.e. trace $\pm 2$. The assertion is that there exist a natural number $n$ and a $\mathbb{Z}$-basis $b$, indexed by $\mathrm{Fin}\,n$, of `parabolicHoms ℤ Γ ℤ` — the group of homomorphisms $\Gamma \to \mathbb{Z}$ killing all elements of trace $\pm 2$ — with the following property: for every field $K$ of characteristic zero, in any universe, there is a $K$-basis $b^K$, again indexed by $\mathrm{Fin}\,n$, of `parabolicHoms K Γ K`, such that for each index $i$ the underlying additive homomorphism $\mathrm{Additive}\,\Gamma \to K$ of $b^K_i$ equals the composite of $b_i$ with the canonical additive map $\mathbb{Z} \to K$. In particular the $K$-dimension of the space of parabolic characters with values in $K$ equals $n$ for every such $K$.
--
--   This records that the parabolic characters of a finite-index subgroup of $\mathrm{SL}(2,\mathbb{Z})$ form a free abelian group of finite rank whose dual basis remains a basis after any base change to a field of characteristic zero, the torsion of the parabolic quotient of $\Gamma^{\mathrm{ab}}$ being invisible to torsion-free targets. It provides the uniform rank used in the Eichler–Shimura comparison for the relevant congruence subgroups and in the construction of the Hecke action on parabolic cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp.lean

import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.LinearAlgebra.Basis.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.Period.exists_basis_parabolicHoms_castAddHom_comp
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ)),
      ∀ (K : Type*) [Field K] [CharZero K],
        ∃ bK : Module.Basis (Fin n) K (ModularCurve.Period.parabolicHoms K Γ K),
          ∀ i, (bK i : Additive Γ →+ K) = (Int.castAddHom K).comp (b i : Additive Γ →+ ℤ) := by sorry
