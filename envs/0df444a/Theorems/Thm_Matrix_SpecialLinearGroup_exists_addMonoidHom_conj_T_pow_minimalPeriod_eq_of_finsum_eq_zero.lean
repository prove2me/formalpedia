-- Prove2me | Theorems.Thm_Matrix_SpecialLinearGroup_exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero
-- name    : Matrix.SpecialLinearGroup.exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/8d457ddf-ccfe-5087-b1aa-22e610006cd1
-- title:
--   Sum-zero functions on cusps realised by homomorphisms of Γ
-- statement:
--   Let $\Gamma$ be a subgroup of finite index in $\mathrm{SL}_2(\mathbb Z)$ containing $-1$, and let $R$ be an additive commutative group. Write $T = \mathrm{ModularGroup.T}$ and let $\langle T\rangle$ be the subgroup of integer powers of $T$, acting by left translation on the coset space $\mathrm{SL}_2(\mathbb Z)/\Gamma$; the quotient of this coset space by the orbit relation of $\langle T\rangle$ is the index set of the statement. Suppose given $a$ from that orbit set to $R$ whose (finitely supported) sum $\sum^{\mathrm f}_c a(c)$ vanishes. The assertion is that there exists an additive group homomorphism $\varphi$ from $\Gamma$, viewed additively, to $R$ with the following property: for every $g \in \mathrm{SL}_2(\mathbb Z)$ and every proof that the element $g^{-1} T^{w} g$ lies in $\Gamma$, where $w$ is the minimal period of the map $x \mapsto T \cdot x$ at the coset $g\Gamma$, the value of $\varphi$ at that element of $\Gamma$ equals $a$ evaluated at the $\langle T\rangle$-orbit of $g\Gamma$.
--
--   In classical language the $\langle T\rangle$-orbits on $\mathrm{SL}_2(\mathbb Z)/\Gamma$ are the cusps of $\Gamma$, $w$ is the width of the cusp through $g\Gamma$ and $g^{-1}T^{w}g$ the corresponding parabolic generator; the statement says that evaluation $\mathrm{Hom}(\Gamma,R) \to R^{\{\text{cusps}\}}$ at the parabolic generators hits every vector of sum zero, so these generators satisfy no relation in $\Gamma^{\mathrm{ab}}$ beyond the boundary relation. It is obtained by transport along $\mathrm{SL}_2(\mathbb Z) \to \mathrm{PSL}_2(\mathbb Z) \cong C_2 * C_3$ from the corresponding statement for a free product, using [`ModularGroup.exists_mulEquiv_freeProduct_quotient_center`](thm.html#ModularGroup.exists_mulEquiv_freeProduct_quotient_center) and [`Monoid.CoprodI.exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero`](thm.html#Monoid.CoprodI.exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero), and is used in the lower bound for the rank of the parabolic homomorphisms in [`ModularCurve.Period.finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one`](thm.html#ModularCurve.Period.finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_SpecialLinearGroup_exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.SpecialLinearGroup.exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ) (R : Type) [AddCommGroup R]
    (a : MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ) → R)
    (ha : ∑ᶠ c, a c = 0) :
    ∃ φ : Additive Γ →+ R,
      ∀ (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
        (hg : g⁻¹ * ModularGroup.T ^ Function.minimalPeriod (fun x => ModularGroup.T • x)
                (g : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ) * g ∈ Γ),
        φ (Additive.ofMul ⟨_, hg⟩)
          = a (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T) _)
              (g : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ)) := by sorry
