-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFY_arrInv_step
-- name    : IntMul.OpenAI.R154.P.NLogN.KFY.arrInv_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T03:18:52.873369+00:00
-- url     : https://prove2.me/theorems/462293f2-ed64-490c-95cd-f9b21e06be12
-- title:
--   arrInv_step (KFY 16: the `A` pass and the `B₀` pass) (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **arrInv_step (KFY 16: the `A` pass and the `B₀` pass)**, at the `frozen-154` constants.
--
--   This is `NLogN.KFY.arrInv_step` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFY 16: the `A` pass and the `B₀` pass*: The arrays keep the invariant `length = ∏ t_i`, `DiscL p` (which gives `GB (p + 2)`), using an
--   `M : AxisMaps` (`disc_sapL`, `disc_b0Pad`).
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFY.arrInv_step` (https://prove2.me/theorems/4ab6c337-0d5a-4493-a1c3-778f0337efd1).

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
open _root_.IntMul.HvdH.Ref hiding bflyB bflyT dcomX dcomY difZ ditZ pmulZ
open _root_.NLogN.GL hiding imE reE rndE
open _root_.NLogN.AX hiding bN
open _root_.NLogN.Rsp hiding BN KN aE cE kE pSt spSt

open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN ZN bN fsA fsB mN mainA mainB mmN overN srcsN tN ΦN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY

theorem IntMul.OpenAI.R154.P.NLogN.KFY.arrInv_step {n : ℕ} (hn : IntMul.OpenAI.Glue.n0 ≤ n) (k : ℕ) (hk : k < IntMul.OpenAI.R154.dP n)
    (f : List KFB.GI → List KFB.GI)
    (hf : ∀ X : List KFB.GI, X.length = tN n k → (f X).length = tN n k)
    (hd : ∀ X, DiscL (IntMul.OpenAI.Glue.pP n) X → DiscL (IntMul.OpenAI.Glue.pP n) (f X)) (X : List KFB.GI)
    (hX : ArrInv n X) : ArrInv n (stepL ((List.ofFn (IntMul.OpenAI.R154.P.NLogN.KFM.tB n)).rotate k) f X) := by sorry
