-- Prove2me | Theorems.Thm_N25_cuspArithmeticCensus_geometric
-- name    : N25.cuspArithmeticCensus_geometric
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:18.948394+00:00
-- url     : https://prove2.me/theorems/225e4933-a233-4867-9e98-cb1892828231
-- title:
--   There are exactly fourteen geometric cusps
-- statement:
--   Fix an embedding $\iota:\overline{\mathbb Q}\hookrightarrow\mathbb C$. Let $F_{\overline{\mathbb Q}}$ be the geometric level-$25$ function field and let $j_{25}$ denote the embedded modular $j$-function. The set of its poles is finite and has cardinality fourteen:
--
--   $$\bigl|\{P:\operatorname{ord}_P(j_{25})<0\}\bigr|=14.$$
--
--   This provides the geometric cusp count used to recover the degrees of the rational closed cusps. Formalization note: $\iota$ supplies the chosen complex comparison and does not occur in the final cardinality formula.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Endgame
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin

set_option autoImplicit false
open ModularCurve AlgebraicCurve
open N25
open N25.Endgame

theorem N25.cuspArithmeticCensus_geometric (ι : Qbar →+* ℂ) :
    Finite {P : GPlace // P.ord (emb25 j25) < 0} ∧
      Nat.card {P : GPlace // P.ord (emb25 j25) < 0} = 14 := by sorry
