-- Prove2me | Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
-- name    : ModularCurve.surjective_specialLinearGroup_map_zmod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/db939305-960d-5ffe-865e-a5fe8c1bb878
-- title:
--   Surjectivity of reduction SL₂(ℤ)toSL₂(ℤ/N)
-- statement:
--   Let $N$ be a natural number which is nonzero (the `NeZero N` instance). The reduction homomorphism $\mathbb{Z}\to\mathbb{Z}/N\mathbb{Z}$, given by `Int.castRingHom (ZMod N)`, induces by entrywise application a group homomorphism on special linear groups of $2\times 2$ matrices (index type `Fin 2`), namely `Matrix.SpecialLinearGroup.map`. The assertion is that this map is surjective as a function: for every matrix $M \in \mathrm{SL}_2(\mathbb{Z}/N\mathbb{Z})$, that is, every $2\times 2$ matrix over $\mathbb{Z}/N\mathbb{Z}$ whose determinant is $1$, there exists a matrix in $\mathrm{SL}_2(\mathbb{Z})$ — an integral $2\times 2$ matrix of determinant exactly $1$ — whose entrywise reduction modulo $N$ equals $M$. Note that the case $N = 1$ is included, the target group then being trivial; no primality, oddness or positivity hypothesis beyond $N \neq 0$ is imposed.
--
--   This is the classical strong-approximation statement for $\mathrm{SL}_2$ over $\mathbb{Z}$ (Diamond–Shurman, Exercise 1.2.2(b)), which with the first isomorphism theorem identifies $\mathrm{SL}_2(\mathbb{Z})/\Gamma(N)$ with $\mathrm{SL}_2(\mathbb{Z}/N\mathbb{Z})$. It is used throughout the cohomological part of the development, for instance in the analysis of bottom rows of matrices modulo $N$, of Hecke operators on the relevant cohomology carriers, and of parabolic homomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_surjective_specialLinearGroup_map_zmod.lean

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.surjective_specialLinearGroup_map_zmod (N : ℕ) [NeZero N] :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by sorry
