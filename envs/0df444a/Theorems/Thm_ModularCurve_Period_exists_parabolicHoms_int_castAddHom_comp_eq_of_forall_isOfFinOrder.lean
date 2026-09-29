-- Prove2me | Theorems.Thm_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder
-- name    : ModularCurve.Period.exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/d9d2beeb-1afd-53f1-b360-95cdb7e8de25
-- title:
--   Integral lifting of parabolic characters mod n vanishing on torsion
-- statement:
--   Let $\Gamma$ be a subgroup of finite index in $\mathrm{SL}_2(\mathbb{Z})$ and let $n$ be a natural number. Let $\varphi$ be an element of [`ModularCurve.Period.parabolicHoms (ZMod n) Γ (ZMod n)`](def/ModularCurve_PeriodMap.html#L62), that is, an additive homomorphism $\varphi\colon \mathrm{Additive}\,\Gamma \to \mathbb{Z}/n\mathbb{Z}$ (a character of $\Gamma$ written additively) which is parabolic in the sense that $\varphi(\gamma) = 0$ for every $\gamma \in \Gamma$ whose underlying integral $2 \times 2$ matrix satisfies $\operatorname{tr}(\gamma)^2 = 4$; these homomorphisms form a $\mathbb{Z}/n\mathbb{Z}$-submodule of $\mathrm{Hom}(\mathrm{Additive}\,\Gamma, \mathbb{Z}/n\mathbb{Z})$. Assume in addition that $\varphi(\gamma) = 0$ for every $\gamma \in \Gamma$ of finite order. The conclusion is that there exists an element $x$ of [`ModularCurve.Period.parabolicHoms ℤ Γ ℤ`](def/ModularCurve_PeriodMap.html#L62), i.e. an additive homomorphism $x\colon \mathrm{Additive}\,\Gamma \to \mathbb{Z}$ vanishing on every $\gamma \in \Gamma$ with $\operatorname{tr}(\gamma)^2 = 4$, such that composing $x$ with the reduction map $\mathbb{Z} \to \mathbb{Z}/n\mathbb{Z}$ gives exactly $\varphi$ as a homomorphism $\mathrm{Additive}\,\Gamma \to \mathbb{Z}/n\mathbb{Z}$. Here $n$ is unrestricted, the cases $n = 0$ and $n = 1$ being included.
--
--   In classical terms the parabolic characters of $\Gamma$ with values in an abelian group $A$ form the parabolic (cuspidal) part of $H^1(\Gamma, A) = \mathrm{Hom}(\Gamma, A)$, which for $A = \mathbb{Z}$ computes the first cohomology of the compactified modular curve attached to $\Gamma$; the statement says that a parabolic class mod $n$ lifts integrally as soon as it kills the torsion of $\Gamma$, reflecting torsion-freeness of the integral parabolic cohomology. It is used in the construction and base change of the period-map carriers of modular cohomology, notably in the results on maximal ideals of Hecke algebras acting on parabolic homomorphism modules and on the $\Gamma_H$-level comparison of such modules, and in the construction of additive homomorphisms from exponential data on elements of trace square at most $4$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.Period.exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (n : ℕ)
    (φ : ModularCurve.Period.parabolicHoms (ZMod n) Γ (ZMod n))
    (hφ : ∀ γ : Γ, IsOfFinOrder γ → (φ : Additive Γ →+ ZMod n) (Additive.ofMul γ) = 0) :
    ∃ x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ,
      (Int.castAddHom (ZMod n)).comp (x : Additive Γ →+ ℤ) = (φ : Additive Γ →+ ZMod n) := by sorry
