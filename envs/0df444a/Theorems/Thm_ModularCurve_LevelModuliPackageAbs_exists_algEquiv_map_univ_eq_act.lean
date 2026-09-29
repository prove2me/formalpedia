-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_map_univ_eq_act
-- name    : ModularCurve.LevelModuliPackageAbs.exists_algEquiv_map_univ_eq_act
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/6d4410df-45c5-5e80-92be-5902a27a6ebd
-- title:
--   Inverse problem automorphisms come from an algebra automorphism
-- statement:
--   Let $A$ be a commutative ring and let $D$ be a level-moduli datum over $A$: an assignment $T \mapsto D.\mathrm{Pt}(T)$ on commutative $A$-algebras together with functorial transport $D.\mathrm{map}$ along $A$-algebra homomorphisms (compatible with identities and composition) and a $j$-invariant map $D.\mathrm{jOf} : D.\mathrm{Pt}(T) \to T$ commuting with transport. Let $P$ be an absolute level-moduli package for $D$: a commutative $A$-algebra $B_0 = P.\mathrm{B}_0$ together with a class $u = P.\mathrm{univ} \in D.\mathrm{Pt}(B_0)$ such that for every commutative $A$-algebra $T$ and every $x \in D.\mathrm{Pt}(T)$ there is a unique $A$-algebra homomorphism $\varphi : B_0 \to T$ with $D.\mathrm{map}\,\varphi\,u = x$. Let $\rho, \rho'$ be problem automorphisms of $D$, that is, self-maps $\rho.\mathrm{act}$ of each $D.\mathrm{Pt}(T)$ commuting with transport along all $A$-algebra homomorphisms and preserving $D.\mathrm{jOf}$, and assume they are mutually inverse pointwise: $\rho'.\mathrm{act}(\rho.\mathrm{act}\,y) = y$ and $\rho.\mathrm{act}(\rho'.\mathrm{act}\,y) = y$ for every commutative $A$-algebra $T$ and every $y \in D.\mathrm{Pt}(T)$. The conclusion is that there exists an $A$-algebra automorphism $\sigma$ of $B_0$ with $D.\mathrm{map}\,\sigma\,u = \rho.\mathrm{act}\,u$ and $D.\mathrm{map}\,\sigma^{-1}\,u = \rho'.\mathrm{act}\,u$.
--
--   This is the Yoneda-type rigidity statement for a representable moduli problem: an invertible natural self-map of the functor is realised on the representing object by an algebra automorphism carrying the universal class to its image. It is the abstract input for the relabelling constructions, being cited by [`ModularCurve.LevelModuliPackageAbs.exists_raw_linComb_algEquiv_map_univ_eq_gamma0Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.exists_raw_linComb_algEquiv_map_univ_eq_gamma0Pow) and [`ModularCurve.LevelModuliPackageAbs.exists_raw_linComb_algEquiv_map_univ_eq_rigidDataH1Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.exists_raw_linComb_algEquiv_map_univ_eq_rigidDataH1Pow), where $\rho$ and $\rho'$ are relabelling by an invertible matrix and by its inverse.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_map_univ_eq_act.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ModularCurve.LevelModuliPackageAbs.exists_algEquiv_map_univ_eq_act
    {A : Type u} [CommRing A] {D : ModularCurve.LevelModuliDatum.{u} A} (P : ModularCurve.LevelModuliPackageAbs A D)
    (ρ ρ' : D.ProblemAut)
    (h₁ : ∀ (T : Type u) [CommRing T] [Algebra A T] (y : D.Pt T), ρ'.act (ρ.act y) = y)
    (h₂ : ∀ (T : Type u) [CommRing T] [Algebra A T] (y : D.Pt T), ρ.act (ρ'.act y) = y) :
    ∃ σ : P.B₀ ≃ₐ[A] P.B₀,
      D.map (σ : P.B₀ →ₐ[A] P.B₀) P.univ = ρ.act P.univ ∧
      D.map (σ.symm : P.B₀ →ₐ[A] P.B₀) P.univ = ρ'.act P.univ := by sorry
