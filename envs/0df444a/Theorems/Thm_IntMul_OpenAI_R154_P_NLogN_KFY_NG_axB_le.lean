-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFY_NG_axB_le
-- name    : IntMul.OpenAI.R154.P.NLogN.KFY.NG.axB_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T03:18:45.022226+00:00
-- url     : https://prove2.me/theorems/451d89eb-62ed-44a0-98d4-aa69c7613e12
-- title:
--   The B₀ axis splits as Ctr + mainB + overN (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **The B₀ axis splits as Ctr + mainB + overN**, at the `frozen-154` constants.
--
--   This is `NLogN.KFY.NG.axB_le` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFY 19: the cost of the two passes for `n` (natural-number part)*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFY.NG.axB_le` (https://prove2.me/theorems/4001f130-1555-4726-8770-12b5942cde0f).

import Definitions.Def_IntMul_OpenAI_R154_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2048
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
variable {n : ℕ} (h : NG n) {k : ℕ} (hk : k < dP n)
include h hk
set_option maxHeartbeats 4000000

open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN ZN bN fsA fsB mN mainA mainB mmN overN srcsN tN ΦN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY
open _root_.NLogN.KFY.NG hiding Lb bl casesOn d5 dbig mk nf rec recOn win2 α4
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY.NG

theorem IntMul.OpenAI.R154.P.NLogN.KFY.NG.axB_le (Kc : ℝ) (Ctr : ℕ) :
    axBC Kc n (tN n k) (IntMul.OpenAI.R154.P.NLogN.KFY.BN n) 30 Ctr
      (bap0AxCostQ (pP n) (IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k) (tN n k) (αP n) (IntMul.OpenAI.R154.P.NLogN.KFY.mN n k) (mmN n) (ΦN n) (BaccN n) (QN n)
        (BqN n)) ≤ Ctr + mainB n + overN n := by sorry
