-- Prove2me | Theorems.Thm_N25_cusp_complex_simple_poles_card_le_five
-- name    : N25.cusp_complex_simple_poles_card_le_five
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:27.573966+00:00
-- url     : https://prove2.me/theorems/c39944dc-7153-4dca-8740-b78e462f0e24
-- title:
--   There are at most five simple poles of $j$ over $\mathbb C$
-- statement:
--   Let $F_{\mathbb C}$ be the complex level-$25$ function field and let $j\in F_{\mathbb C}$ have the standard $j$-series. The set of places at which $j$ has order $-1$ is finite and has cardinality at most five:
--
--   $$\bigl|\{P:\operatorname{ord}_P(j)=-1\}\bigr|\le5.$$
--
--   This bounds the number of width-one geometric cusps.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_ord_eq_neg_width_of_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_exists_tendsto_realizeOf_mul_exp_of_not_mem_toValuationSubring

set_option autoImplicit false
open ModularCurve AlgebraicCurve CongruenceSubgroup
open scoped MatrixGroups Topology
open N25

theorem N25.cusp_complex_simple_poles_card_le_five
    (j : laurentBaseChange ℂ (xHFunctionField 25 N25.H25))
    (hj : (j : LaurentSeries ℂ) = jqModC ℂ) :
    Finite {P : Place ℂ (laurentBaseChange ℂ (xHFunctionField 25 N25.H25)) // P.ord j = -1} ∧
      Nat.card {P : Place ℂ (laurentBaseChange ℂ (xHFunctionField 25 N25.H25)) // P.ord j = -1} ≤ 5 := by sorry
