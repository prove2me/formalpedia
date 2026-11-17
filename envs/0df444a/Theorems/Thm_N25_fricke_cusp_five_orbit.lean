-- Prove2me | Theorems.Thm_N25_fricke_cusp_five_orbit
-- name    : N25.fricke_cusp_five_orbit
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:09.590243+00:00
-- url     : https://prove2.me/theorems/5007f3c0-590f-4669-9c71-9274fbfa3c2b
-- title:
--   All width-$25$ geometric cusps form one five-element Galois orbit
-- statement:
--   Fix $\iota:\overline{\mathbb Q}\hookrightarrow\mathbb C$ and the Fricke matrix $W=\begin{pmatrix}0&-1\25&0\end{pmatrix}$. There exists a geometric field automorphism $w$ such that the places $P_i=w_*^{-1}p_i$ satisfy
--
--   $$\operatorname{ord}_{P_i}(j_{25})=-25,$$
--
--    the map $i\mapsto P_i$ is injective, some Galois element cyclically sends $P_i$ to $P_{i+1}$, none of the $P_i$ is rational, every pair $P_i,P_j$ is Galois conjugate, and every geometric place of $j$-order $-25$ equals one of the $P_i$. This completely identifies the width-$25$ cusp orbit.
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
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul
import Theorems.Thm_ModularCurve_coe_apply_eq_qExpand_jqModC_of_forall_coeffMap_mul_qExpansion_slash_fricke_eq

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open ModularCurve AlgebraicCurve
open scoped MatrixGroups ModularForm Pointwise
open N25
open N25.Endgame

theorem N25.fricke_cusp_five_orbit (ι : Qbar →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (25 : ℝ), 0]) :
    ∃ w : FG ≃ₐ[Qbar] FG,
      let family : Fin 5 → GPlace := fun i => SemilinearAut.ofAlgAut w.symm • pG25 i
      (∀ i : Fin 5, (family i).ord (emb25 j25) = -25) ∧
      Function.Injective family ∧
      (∃ σ : Gal, ∀ i : Fin 5, arithmeticGalois FQ σ • family i = family (i+1)) ∧
      (∀ i : Fin 5, ¬ IsRationalGeomPlace (family i)) ∧
      (∀ i j : Fin 5, ∃ σ : Gal, arithmeticGalois FQ σ • family i = family j) ∧
      ∀ P : GPlace, P.ord (emb25 j25) = -25 → ∃ i : Fin 5, P = family i := by sorry
