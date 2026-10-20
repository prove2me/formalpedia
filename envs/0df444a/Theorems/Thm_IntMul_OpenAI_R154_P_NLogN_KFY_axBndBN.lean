-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFY_axBndBN
-- name    : IntMul.OpenAI.R154.P.NLogN.KFY.axBndBN
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-20T03:21:42.1464+00:00
-- url     : https://prove2.me/theorems/08d1734a-f4de-4396-866e-182f5d452253
-- title:
--   axBndBN (KFY 17: the numeric parameters of the passes) (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **axBndBN (KFY 17: the numeric parameters of the passes)**, at the `frozen-154` constants.
--
--   This is `NLogN.KFY.axBndBN` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFY 17: the numeric parameters of the passes*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFY.axBndBN` (https://prove2.me/theorems/c18ff6fa-14e8-4105-83f3-6f35792db49b).

import Definitions.Def_IntMul_OpenAI_R154_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN ZN bN fsA fsB mN mainA mainB mmN overN srcsN tN ΦN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY
open _root_.IntMul
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.NLogN.GL hiding imE reE rndE
open _root_.NLogN.AX hiding bN
open _root_.NLogN.Rsp hiding BN KN aE cE kE pSt spSt

open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN ZN bN fsA fsB mN mainA mainB mmN overN srcsN tN ΦN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY

theorem IntMul.OpenAI.R154.P.NLogN.KFY.axBndBN {n : ℕ} (h : NF n) : AxBndB n (AN n) (IntMul.OpenAI.R154.P.NLogN.KFY.BN n) := by sorry
