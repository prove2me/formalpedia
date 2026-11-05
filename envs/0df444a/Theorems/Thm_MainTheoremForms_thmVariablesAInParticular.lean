-- Prove2me | Theorems.Thm_MainTheoremForms_thmVariablesAInParticular
-- name    : MainTheoremForms.thmVariablesAInParticular
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:41:28.919202+00:00
-- url     : https://prove2.me/theorems/a3525d87-6933-439b-83be-051f172b115e
-- title:
--   Main Theorem Forms: thm Variables AIn Particular
-- statement:
--   Theorem D (a), last sentence: if e_ℓ ≤ c·(log K_ℓ)^(−α′) for all ℓ, with α′ > 0, a machine with
--   the bound of Theorem D (a) takes at most 2^{C'·k²·n·log log n/(log n)^α′} steps, for n ≥ K₀^17 and 3
--   ≤ k ≤ (log n)^(1/4).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/ThmVariablesA.lean#L54-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/ThmVariablesA.lean#L54-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
import Definitions.Def_VariableBound_Printed_VariablesA_Setting
import Definitions.Def_VariableBound_Printed_VariablesA_Main
import Definitions.Def_VariableBound_Params_Ineq
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_ParityChecks_CertOL
import Definitions.Def_UniformInK_Cert_Top
import Definitions.Def_UniformInK_Tree_Tree
import Definitions.Def_UniformInK_Tree_Defs
import Definitions.Def_UniformInK_Tree_Stack
import Definitions.Def_UniformInK_Spars_Main
import Definitions.Def_UniformInK_Cert_Walk
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_UniformInK_Top_ArithDefs
import Definitions.Def_FixedWidthVariableBoundStatement
import Definitions.Def_ClauseBound_ParityChecks_MasterOL
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_CertTopNet
import Definitions.Def_PaddedDescent_Col_CertG
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_CountKSatRate_Walk
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSat_InOut
import Definitions.Def_VariableBound_Printed_ThmVariablesA
import Theorems.Thm_VariableBound_VariablesA_thmVariablesAInParticular

set_option autoImplicit false
section
section
open MainTheoremForms
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.ParityChecks UniformInK VariableBound.VariablesA

theorem MainTheoremForms.thmVariablesAInParticular : ThmVariablesAInParticular := by sorry
