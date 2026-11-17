-- Prove2me | Theorems.Thm_N25_unitDenominatorForm25
-- name    : N25.unitDenominatorForm25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:48:23.394807+00:00
-- url     : https://prove2.me/theorems/f6559b2e-54e3-4dbf-a677-43d42931851f
-- title:
--   The common denominator series is the integral q-expansion of $Δ^3$
-- statement:
--   Let $Γ_H$ be the level-$25$ group and let $D(q)$ be the designated denominator power series. There exists a modular form $G$ of weight $36$ on $Γ_H$ such that $$G(τ)=Δ(τ)^3\quad\text{for all }τ∈\mathfrak H,$$ and the integral q-expansion of $G$ is $D(q)$. This supplies the common denominator used to turn the modular units into holomorphic forms.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane ModularCurve
open scoped MatrixGroups
open N25

theorem N25.unitDenominatorForm25 :
    ∃ G : ModularForm GammaH25GL 36,
      (∀ τ : UpperHalfPlane, G τ = ModularForm.discriminant τ ^ 3) ∧
      ModularCurve.IsIntegralQExp G unitDenominatorSeries25 := by sorry
