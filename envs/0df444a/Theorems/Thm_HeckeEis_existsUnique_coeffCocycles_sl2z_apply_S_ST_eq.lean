-- Prove2me | Theorems.Thm_HeckeEis_existsUnique_coeffCocycles_sl2z_apply_S_ST_eq
-- name    : HeckeEis.existsUnique_coeffCocycles_sl2z_apply_S_ST_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/d7a4a089-f9e4-5ac3-ad7a-d7d440ac13f4
-- title:
--   Cocycles on SL₂(ℤ) determined by z(S), z(ST)
-- statement:
--   Let $K$ be a commutative ring, $V$ a $K$-module, and $\rho$ a representation of $\mathrm{SL}_2(\mathbb{Z})$ (the special linear group of $2\times 2$ integer matrices) on $V$ over $K$. Let $x, y \in V$ satisfy the two torsion conditions $x + \rho(S)x = 0$, where $S$ is the matrix `ModularGroup.S`, and $y + \rho(ST)y + \rho(ST)\bigl(\rho(ST)y\bigr) = 0$, where $ST$ is the product of `ModularGroup.S` and `ModularGroup.T` (the third summand is written as $\rho(ST)$ applied twice rather than as $\rho((ST)^2)$). Then there is exactly one element $z$ of the $K$-submodule [`HeckeEis.coeffCocycles`](def/Gamma0CoeffCohomology.html#L13) $\rho$ of $V$-valued functions on $\mathrm{SL}_2(\mathbb{Z})$ — that is, exactly one function $z \colon \mathrm{SL}_2(\mathbb{Z}) \to V$ with $z(gh) = z(g) + \rho(g)(z(h))$ for all $g, h$ — whose value at $S$ is $x$ and whose value at $ST$ is $y$. Thus the two displayed conditions on $x$ and $y$ are not merely necessary but also sufficient, and a $1$-cocycle for $\rho$ is freely and uniquely prescribed by its values at $S$ and at $ST$.
--
--   This is the cocycle form of the presentation $\mathrm{SL}_2(\mathbb{Z}) \cong \mathbb{Z}/4 *_{\mathbb{Z}/2} \mathbb{Z}/6$ with generators $S$ of order $4$ and $ST$ of order $6$: the space $Z^1(\mathrm{SL}_2(\mathbb{Z}), V)$ is identified with $\ker(1 + \rho(S)) \times \ker(1 + \rho(ST) + \rho(ST)^2)$. It is used in the construction of explicit $1$-cocycles attached to Eisenstein series and in the computation of the Hecke eigensystem on the resulting cohomology classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_existsUnique_coeffCocycles_sl2z_apply_S_ST_eq.lean

import Mathlib
import Definitions.Def_Gamma0CoeffCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HeckeEis.existsUnique_coeffCocycles_sl2z_apply_S_ST_eq
    (K : Type*) [CommRing K] (V : Type*) [AddCommGroup V] [Module K V]
    (ρ : Representation K (Matrix.SpecialLinearGroup (Fin 2) ℤ) V) (x y : V)
    (hx : x + ρ ModularGroup.S x = 0)
    (hy : y + ρ (ModularGroup.S * ModularGroup.T) y
        + ρ (ModularGroup.S * ModularGroup.T) (ρ (ModularGroup.S * ModularGroup.T) y) = 0) :
    ∃! z : ↥(HeckeEis.coeffCocycles ρ),
      (z : Matrix.SpecialLinearGroup (Fin 2) ℤ → V) ModularGroup.S = x
        ∧ (z : Matrix.SpecialLinearGroup (Fin 2) ℤ → V) (ModularGroup.S * ModularGroup.T) = y := by sorry
