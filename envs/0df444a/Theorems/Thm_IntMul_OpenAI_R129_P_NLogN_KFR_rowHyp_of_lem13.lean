-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFR_rowHyp_of_lem13
-- name    : IntMul.OpenAI.R129.P.NLogN.KFR.rowHyp_of_lem13
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:23.532931+00:00
-- url     : https://prove2.me/theorems/94c1b55b-8fed-44df-a4da-f1d47b0adb48
-- title:
--   The bridge: Lemma 13 (Lem13ILP iprog) gives the row hypothesis of KFN with τ50 (κ = 2⁻¹²⁹ constants)
-- statement:
--   **The bridge: Lemma 13 (Lem13ILP iprog) gives the row hypothesis of KFN with τ50**, at the `same-network-129` constants.
--
--   This is `NLogN.KFR.rowHyp_of_lem13` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFR: the bridge `Lem13ILP iprog → RowHyp … τ50`*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFR.rowHyp_of_lem13` (https://prove2.me/theorems/56bcb918-3011-45e6-a852-c0f38d118ac9).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open _root_.NLogN
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFR hiding Lem13Body Lem13IL Lem13ILP bnd
open _root_.IntMul.OpenAI.R129.P.NLogN.KFR
open Complex
open _root_.IntMul
open _root_.NLogN.RS
open _root_.AModel hiding hdPos
open _root_.NLogN.KIL hiding Cfg FR St aE negP outR padL
open _root_.NLogN.KFD
open _root_.NLogN.KFB hiding permL permP
open _root_.NLogN.KFG hiding imE reE
open _root_.NLogN.KFH
open _root_.P8Lift
open _root_.Butterfly hiding Op
open _root_.NLogN.KFN hiding pcs τ50
open _root_.IntMul.OpenAI.R129.P.NLogN.KFN

open _root_.NLogN
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFR hiding Lem13Body Lem13IL Lem13ILP bnd
open _root_.IntMul.OpenAI.R129.P.NLogN.KFR

theorem IntMul.OpenAI.R129.P.NLogN.KFR.rowHyp_of_lem13 {iprog : Fin 1 → IStmt HS 1} (H : Lem13ILP iprog) :
    ∃ Kc : ℝ, 0 < Kc ∧ ∀ (Isym : List Sym) {K m r Z : ℕ}, 6 ≤ K → 3 ≤ m → 1 ≤ r →
      80 * Z * (Z + 2) ≤ 2 ^ K →
      RowHyp Isym iprog K m r Z (PsiR r Z) (Kc * (K + 2) + 1) τ50 := by sorry
