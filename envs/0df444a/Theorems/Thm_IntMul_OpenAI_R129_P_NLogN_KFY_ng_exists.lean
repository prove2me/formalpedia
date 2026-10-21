-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFY_ng_exists
-- name    : IntMul.OpenAI.R129.P.NLogN.KFY.ng_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:43.682223+00:00
-- url     : https://prove2.me/theorems/7b70e479-4b8e-4bdb-8aaa-5a5912f4baf5
-- title:
--   ng_exists (KFY 19: the cost of the two passes for `n` (natural-number part)) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **ng_exists (KFY 19: the cost of the two passes for `n` (natural-number part))**, at the `same-network-129` constants.
--
--   This is `NLogN.KFY.ng_exists` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFY 19: the cost of the two passes for `n` (natural-number part)*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFY.ng_exists` (https://prove2.me/theorems/3b4827a5-419b-4913-8683-cc071d2d3b42).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2048
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN TrHyp ZN axA axB bN fsA fsB mN mainA mainB mmN overN progA progB srcsN tN trBlk trBound trC trPrc ΦN
open _root_.IntMul.OpenAI.R129.P.NLogN.KFY
open _root_.IntMul
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R129
open _root_.NLogN.GL hiding imE reE rndE
open _root_.NLogN.AX hiding bN
open _root_.NLogN.Rsp hiding BN KN aE cE kE pSt spSt

open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN TrHyp ZN axA axB bN fsA fsB mN mainA mainB mmN overN progA progB srcsN tN trBlk trBound trC trPrc ΦN
open _root_.IntMul.OpenAI.R129.P.NLogN.KFY

theorem IntMul.OpenAI.R129.P.NLogN.KFY.ng_exists : ∃ n₂, ∀ n, IntMul.OpenAI.Glue.n0 ≤ n → n₂ ≤ n → NG n := by sorry
