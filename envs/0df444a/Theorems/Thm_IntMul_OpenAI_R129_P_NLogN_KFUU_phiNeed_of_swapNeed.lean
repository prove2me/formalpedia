-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFUU_phiNeed_of_swapNeed
-- name    : IntMul.OpenAI.R129.P.NLogN.KFUU.phiNeed_of_swapNeed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:18.124659+00:00
-- url     : https://prove2.me/theorems/964e9d08-f4ed-4b4c-b616-6dae4858ecab
-- title:
--   SwapNeed → PhiNeed (κ = 2⁻¹²⁹ constants)
-- statement:
--   **SwapNeed → PhiNeed**, at the `same-network-129` constants.
--
--   This is `NLogN.KFUU.phiNeed_of_swapNeed` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFUU §10: `SwapNeed → PhiNeed`*: The table is KFM's merged table `mTable ext₁ ∅ ∅ own` (`KFM.mExt`): the `SwapNeed` extensions
--   relabelled (`IRuns.relabel` via `KFM.mTable_g1`), then `own = [phiFU, phiBU]`. The swap entry
--   of the reversals is the relabelled `SwapNeed` entry. Costs: `cFwd`, `cBwd ≤ natCost + (d+1)·cSwV`
--   and `natCost_le`, `swq_le` absorb everything into `(C₁ + 781 K) · cPhiU`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFUU.phiNeed_of_swapNeed` (https://prove2.me/theorems/7d7bb3c0-c5ba-4ea7-8787-c9f852efcc51).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
open _root_.NLogN hiding cE mvK tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFUU hiding SwOKU cBwd cFwd cRevU cSwN cSwV cTr
open _root_.IntMul.OpenAI.R129.P.NLogN.KFUU
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR PushOK St aE cBwd cFwd dP dropK negP outR padL postB preB shP sufV tB xA
open _root_.NLogN.KFB hiding mvL permL permP rB
open _root_.NLogN.KFC hiding enc encF isPos rW
open _root_.NLogN.KFT hiding tE tT
open _root_.NLogN.KFU hiding SwOK cPhi oD
open _root_.IntMul.OpenAI.R129.P.NLogN.KFU
open _root_.AModel hiding hdPos
open _root_.AModelL12
set_option maxHeartbeats 4000000

open _root_.NLogN hiding cE mvK tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFUU hiding SwOKU cBwd cFwd cRevU cSwN cSwV cTr
open _root_.IntMul.OpenAI.R129.P.NLogN.KFUU

theorem IntMul.OpenAI.R129.P.NLogN.KFUU.phiNeed_of_swapNeed (hsw : IntMul.OpenAI.R129.P.NLogN.KFM.SwapNeed) : IntMul.OpenAI.R129.P.NLogN.KFM.PhiNeed := by sorry
