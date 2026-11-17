-- Prove2me | Theorems.Thm_N25_cusp_coefficient_embedding
-- name    : N25.cusp_coefficient_embedding
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:48.564627+00:00
-- url     : https://prove2.me/theorems/ba09f1e8-cb35-44a8-b62c-382726d0cfa8
-- title:
--   The geometric function field embeds coefficientwise into its complex base change
-- statement:
--   Fix an embedding $\iota:\overline{\mathbb Q}\hookrightarrow\mathbb C$. Let $F_0$ be the rational level-$25$ function field, $F$ its base change to $\overline{\mathbb Q}$, and $F_{\mathbb C}$ its base change to $\mathbb C$. There exists a ring homomorphism $\kappa:F\to F_{\mathbb C}$ such that Laurent coefficients are mapped by $\iota$, constants satisfy $\kappa(a)=\iota(a)$, the induced towers $\overline{\mathbb Q}\subseteq\mathbb C\subseteq F_{\mathbb C}$ and $\overline{\mathbb Q}\subseteq F\subseteq F_{\mathbb C}$ are scalar towers, and
--
--   $$\mathbb C\bigl(\kappa(F)\bigr)=F_{\mathbb C}.$$
--
--   This supplies the coefficient-compatible field embedding used to compare algebraic and analytic cusps. Formalization note: the three displayed algebra structures are explicit bookkeeping for the two scalar towers.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open ModularCurve
open N25

theorem N25.cusp_coefficient_embedding
    (ι : AlgebraicClosure ℚ →+* ℂ) :
    let K := AlgebraicClosure ℚ
    let F₀ := xHFunctionField 25 N25.H25
    let F := xHFunctionFieldBar 25 N25.H25
    let Fℂ := laurentBaseChange ℂ F₀
    ∃ κ : F →+* Fℂ,
      (∀ x : F, (κ x : LaurentSeries ℂ) = coeffMap ι (x : LaurentSeries K)) ∧
      (∀ a : K, κ (algebraMap K F a) = algebraMap ℂ Fℂ (ι a)) ∧
      (letI : Algebra K ℂ := ι.toAlgebra
       letI : Algebra K Fℂ := ((algebraMap ℂ Fℂ).comp ι).toAlgebra
       letI : Algebra F Fℂ := κ.toAlgebra
       IsScalarTower K ℂ Fℂ ∧ IsScalarTower K F Fℂ ∧
         IntermediateField.adjoin ℂ (Set.range κ) = ⊤) := by sorry
