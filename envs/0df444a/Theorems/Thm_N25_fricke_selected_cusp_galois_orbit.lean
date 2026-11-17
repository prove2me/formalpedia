-- Prove2me | Theorems.Thm_N25_fricke_selected_cusp_galois_orbit
-- name    : N25.fricke_selected_cusp_galois_orbit
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:18.353194+00:00
-- url     : https://prove2.me/theorems/57a7c6a7-3b4a-4df4-ae29-86ea982a9435
-- title:
--   Fricke–Galois compatibility makes the transformed cusp family a transitive orbit
-- statement:
--   Let $w$ be a geometric function-field automorphism such that whenever $\sigma$ acts on $25$th roots by $\zeta\mapsto\zeta^c$, one has $w(\sigma x)=\sigma\delta_c(wx)$ for every $x$. Define $P_i=w_*^{-1}p_i$. Then
--
--   $$i\mapsto P_i\text{ is injective and }\{P_0,\ldots,P_4\}\text{ is one transitive Galois orbit},$$
--
--    with a Galois element cycling $P_i$ to $P_{i+1}$, and no $P_i$ is a rational geometric place. This extracts the orbit structure solely from the Fricke–Galois intertwining law.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_LocalKummerCharacter
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_diamondAutHBar_mul_and_diamondAutHBar_one
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Theorems.Thm_ModularCurve_diamondAutHBar_eq_refl_of_mem_or_neg_mem

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open ModularCurve AlgebraicCurve
open scoped MatrixGroups Pointwise
open N25
open N25.Endgame

theorem N25.fricke_selected_cusp_galois_orbit
    (w : FG ≃ₐ[Qbar] FG)
    (hgal : ∀ (σ : Gal) (c : ℕ) (hc : c.Coprime 25),
      (∀ ζ : Qbar, ζ ^ 25 = 1 → σ ζ = ζ ^ c) →
      ∀ x : FG, w (arithmeticGalois FQ σ • x) =
        arithmeticGalois FQ σ • diamondAutHBar 25 H25 (ZMod.unitOfCoprime c hc) (w x)) :
    Function.Injective (fun i : Fin 5 => SemilinearAut.ofAlgAut w.symm • pG25 i) ∧
    (∃ σ : Gal, ∀ i : Fin 5,
      arithmeticGalois FQ σ • (SemilinearAut.ofAlgAut w.symm • pG25 i) =
        SemilinearAut.ofAlgAut w.symm • pG25 (i+1)) ∧
    (∀ i : Fin 5, ¬ IsRationalGeomPlace (SemilinearAut.ofAlgAut w.symm • pG25 i)) ∧
    ∀ i j : Fin 5, ∃ σ : Gal,
      arithmeticGalois FQ σ • (SemilinearAut.ofAlgAut w.symm • pG25 i) =
        SemilinearAut.ofAlgAut w.symm • pG25 j := by sorry
