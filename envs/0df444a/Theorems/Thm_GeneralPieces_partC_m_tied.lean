-- Prove2me | Theorems.Thm_GeneralPieces_partC_m_tied
-- name    : GeneralPieces.partC_m_tied
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T01:52:04.270854+00:00
-- url     : https://prove2.me/theorems/cd47d434-0783-4f56-bd95-a163a0b327c3
-- title:
--   General Pieces: part C m tied
-- statement:
--   Part (c), first sentence, for the named programs: pieces whose numbers of bits are at most 2λ
--   and any x₀ of the theorem. The network of the formula is rebalanced by case (i) of Lemma 8
--   (`Top.stCountG2`); the exponent is bounded through the display in the paper's proof of part (c) and
--   "every term after 2ekm is O(k·m^{1−1/90})" (`TopDisplay.top_level`, `top_arith`); the level is "the
--   largest ℓ with K_ℓ ≤ m^{1/9}", and e_ℓ = O((log m)^{−α'}) there by
--   part (a) (`PartAUse.e_le_rPow`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/ThmRunningTime.lean#L98-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/ThmRunningTime.lean#L98-L110

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_GeneralPieces_Rec_PartB
import Definitions.Def_GeneralPieces_Rec_Seq
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_Num_PartD
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Definitions.Def_GeneralPieces_DefGenPieces_MayAssume
import Definitions.Def_ClauseBound_Gen_End
import Definitions.Def_ClauseBound_ParityChecks_MasterOL
import Definitions.Def_GeneralPieces_Top_CaseI
import Definitions.Def_GeneralPieces_Top_EndM
import Definitions.Def_ClauseBound_ParityChecks_MasterOL
import Definitions.Def_ClauseBound_ParityChecks_MasterOL
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Gen
import Definitions.Def_ClauseBound_TopN_Gen
import Definitions.Def_ClauseBound_Alg_NeedC
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_TopVal
import Definitions.Def_ClauseBound_Alg_CertTop
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_ClauseBound_ParityChecks_EndOL
import Definitions.Def_ClauseBound_ParityChecks_TopOL
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Definitions.Def_ClauseBound_ParityChecks_CertOL
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Definitions.Def_ClauseBound_ParityChecks_Ev
import Definitions.Def_ClauseBound_ParityChecks_Count
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Definitions.Def_ClauseBound_ParityChecks_Bridge
import Definitions.Def_ClauseBound_ParityChecks_ChoiceByPotential
import Definitions.Def_ClauseBound_TopN_Budget
import Definitions.Def_ClauseBound_TopN_Walk
import Definitions.Def_ClauseBound_Alg_CertTopNet
import Definitions.Def_PaddedDescent_F_MarkCode
import Definitions.Def_PaddedDescent_F_MarkVal
import Definitions.Def_PaddedDescent_F_MarkProf
import Definitions.Def_PaddedDescent_F_MarkSize
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_CountKSatRate_Tree
import Definitions.Def_CountKSatRate_Walk
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSatRate_Stack
import Definitions.Def_CountKSat_InOut
import Definitions.Def_GeneralPieces_ThmRunningTime
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen

theorem GeneralPieces.partC_m_tied {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hP : Par P ρ c) (hm : P.m = 1) (hKeeps : P.Keeps) (hx : 18 ≤ x₀)
    (hc : c + 5 ≤ 2 ^ x₀) : Tied.PartCm P ρ x₀ := by sorry
