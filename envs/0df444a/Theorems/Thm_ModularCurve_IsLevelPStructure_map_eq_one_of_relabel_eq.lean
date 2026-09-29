-- Prove2me | Theorems.Thm_ModularCurve_IsLevelPStructure_map_eq_one_of_relabel_eq
-- name    : ModularCurve.IsLevelPStructure.map_eq_one_of_relabel_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/1bc36d82-d58d-531a-9cc6-0b02a3bf40a3
-- title:
--   Relabelling acts freely on level-ℓ structures
-- statement:
--   Let $F$ be a field, let $\ell\ge 3$ be a prime with $\ell\neq 0$ in $F$, and let $W$ be a Weierstrass curve over $F$ whose discriminant $W.\Delta$ is a unit. Let $D$ be a `LevelPData F`, i.e. a quadruple of elements $x_P,y_P,x_Q,y_Q$ of $F$, and assume `IsLevelPStructure W ℓ D`: both pairs $(x_P,y_P)$ and $(x_Q,y_Q)$ satisfy the affine Weierstrass equation of $W$, the $\ell$-th division polynomial value $(W.\mathrm{pre}\Psi\,\ell)$ vanishes at $x_P$ and at $x_Q$, and both elements $\mathrm{indepElt}\,W\,\ell\,x_P\,x_Q$ and $\mathrm{indepElt}\,W\,\ell\,x_Q\,x_P$ are units, where $\mathrm{indepElt}\,W\,p\,x_0\,x=\prod_{a=1}^{(p-1)/2}\bigl(x\,(W.\Psi^2_a)(x_0)-(W.\Phi_a)(x_0)\bigr)$. Let $g$ be a $2\times 2$ matrix over $\mathbb{Z}$ whose reduction modulo $\ell$ has unit determinant, and suppose $D$ is fixed by relabelling along $g$: writing $P$ and $Q$ for the affine points attached to $(x_P,y_P)$ and $(x_Q,y_Q)$ (the point itself when nonsingular, and $0$ otherwise), and passing back to coordinates by sending $0$ to $(0,0)$ and a point to its pair of coordinates, the quadruple obtained from $g_{00}\cdot P+g_{10}\cdot Q$ and $g_{01}\cdot P+g_{11}\cdot Q$ equals $D$. Then the reduction of $g$ modulo $\ell$ is the identity matrix in $M_2(\mathbb{Z}/\ell)$.
--
--   This is the rigidity (freeness) statement for the $\mathrm{GL}_2(\mathbb{Z}/\ell)$-relabelling action on level-$\ell$ structures written in division-polynomial coordinates: a matrix fixing such a structure is trivial modulo $\ell$. It is used in the analysis of the action on the moduli package, in [`ModularCurve.LevelModuliPackageAbs.u_pow_sub_one_mem_and_of_act_mapRing_eq_relabel_gamma0Pow_of_mem_ssJSet`](thm.html#ModularCurve.LevelModuliPackageAbs.u_pow_sub_one_mem_and_of_act_mapRing_eq_relabel_gamma0Pow_of_mem_ssJSet).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsLevelPStructure_map_eq_one_of_relabel_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.IsLevelPStructure.map_eq_one_of_relabel_eq
    {F : Type} [Field F] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓF : (ℓ : F) ≠ 0)
    (W : WeierstrassCurve F) (hΔ : IsUnit W.Δ)
    (D : ModularCurve.LevelPData F) (hD : ModularCurve.IsLevelPStructure W ℓ D)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det)
    (h : ModularCurve.LevelRelabelling.LevelPData.relabel W g D = D) :
    g.map (Int.castRingHom (ZMod ℓ)) = 1 := by sorry
