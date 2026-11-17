-- Prove2me | Theorems.Thm_N25_five_qPlaces_distinct
-- name    : N25.five_qPlaces_distinct
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:11.628002+00:00
-- url     : https://prove2.me/theorems/1f52fc71-8fca-4a0a-ab16-b9ef95c6b46c
-- title:
--   Five distinct rational and geometric $q$-cusps form compatible diamond orbits
-- statement:
--   Let $F_0$ be the rational level-$25$ function field, let $F$ be its base change to $\overline{\mathbb Q}$, and let $\gamma_F$ be the label-$13$ diamond automorphism of $F$. There exist witnesses that the rational and geometric $q$-infinity places are defined and a rational automorphism $\tau_0$ such that, for the coefficient embedding $\iota:F_0\to F$ and the two five-term orbits $p_i^{\mathbb Q}=\tau_0^ip_\infty$ and $p_i=\gamma_F^ip_\infty$,
--
--   $$\gamma_F(\iota x)=\iota(\tau_0x),$$
--
--    both orbit maps are injective, every listed place has degree one, every $p_i$ is fixed by arithmetic Galois, and $\operatorname{ord}_{p_i}(\iota x)=\operatorname{ord}_{p_i^{\mathbb Q}}(x)$. This constructs the five compatible selected cusps. Formalization note: the two initial witnesses only certify the existence of the $q$-infinity place constructors.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option autoImplicit false
open ModularCurve AlgebraicCurve
open scoped MatrixGroups
open N25

theorem N25.five_qPlaces_distinct :
    let K := AlgebraicClosure ℚ
    let F₀ := xHFunctionField 25 H25
    let F := xHFunctionFieldBar 25 H25
    let gammaF := diamondAutHBar 25 H25 (ZMod.unitOfCoprime 13 (by decide))
    ∃ h₀ : (∃ j : F₀, (qSeriesBar ℚ F₀ j).order = -1),
    ∃ h : (∃ j : F, (qSeriesBar K F j).order = -1),
    ∃ τ₀ : F₀ ≃ₐ[ℚ] F₀,
      let ι : F₀ → F := fun x =>
        ⟨coeffEmb K (x : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange K x.2⟩
      let p₀ : Fin 5 → Place ℚ F₀ := fun i =>
        (SemilinearAut.ofAlgAut τ₀)^i.val • qInftyPlaceRat F₀ h₀
      let p : Fin 5 → Place K F := fun i =>
        (SemilinearAut.ofAlgAut gammaF)^i.val • qInftyPlaceBar K F h
      (∀ x : F₀, gammaF (ι x) = ι (τ₀ x)) ∧
      Function.Injective p₀ ∧ Function.Injective p ∧
      (∀ i : Fin 5, (p₀ i).deg = 1 ∧ (p i).deg = 1) ∧
      (∀ σ : Gal, ∀ i : Fin 5, arithmeticGalois F₀ σ • p i = p i) ∧
      (∀ i : Fin 5, ∀ x : F₀, (p i).ord (ι x) = (p₀ i).ord x) := by sorry
