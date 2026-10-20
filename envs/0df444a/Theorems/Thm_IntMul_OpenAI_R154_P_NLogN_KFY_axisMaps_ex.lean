-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFY_axisMaps_ex
-- name    : IntMul.OpenAI.R154.P.NLogN.KFY.axisMaps_ex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-20T03:21:36.435411+00:00
-- url     : https://prove2.me/theorems/a340c478-3876-4e6f-ac09-d3e6feab223b
-- title:
--   No prc node. -/ def noPrc : RM → Bool | .rs _ | .mul _ _ _ | .op _ => true | .seq a b | .ite _ a b =>… (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **No prc node. -/ def noPrc : RM → Bool | .rs _ | .mul _ _ _ | .op _ => true | .seq a b | .ite _ a b =>…**, at the `frozen-154` constants.
--
--   This is `NLogN.KFY.axisMaps_ex` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFY 21: `TransNeed → LineNeed`*: The descriptor stack is `dS = 26`; `C₀ = 17 K + 1 + 216·10^14 · cZ · 4 · 58^6`, `A = 6`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFY.axisMaps_ex` (https://prove2.me/theorems/0358e6e0-b0c8-4ce0-88cc-315bee23519a).

import Definitions.Def_IntMul_OpenAI_R154_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
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
open _root_.IntMul.HvdH.Ref hiding bflyB bflyT dcomX dcomY difZ ditZ pmulZ
open _root_.NLogN.KIL hiding Cfg FR St aE negP outR padL yB
open _root_.NLogN.KFB hiding blk cZ permL permP

open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN ZN bN fsA fsB mN mainA mainB mmN overN srcsN tN ΦN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY

theorem IntMul.OpenAI.R154.P.NLogN.KFY.axisMaps_ex : ∃ n₂, ∀ n, IntMul.OpenAI.Glue.n0 ≤ n → n₂ ≤ n →
    ∀ [∀ i, NeZero (IntMul.OpenAI.R154.P.NLogN.KFM.sB n i)] [∀ i, NeZero (IntMul.OpenAI.R154.P.NLogN.KFM.tB n i)],
    Nonempty (KFM.AxisMaps (d := IntMul.OpenAI.R154.dP n) (pP n) (αP n) (IntMul.OpenAI.R154.P.NLogN.KFM.sB n) (IntMul.OpenAI.R154.P.NLogN.KFM.tB n)) := by sorry
