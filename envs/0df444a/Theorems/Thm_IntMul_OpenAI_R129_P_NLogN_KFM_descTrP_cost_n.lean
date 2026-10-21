-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFM_descTrP_cost_n
-- name    : IntMul.OpenAI.R129.P.NLogN.KFM.descTrP_cost_n
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:26:40.496327+00:00
-- url     : https://prove2.me/theorems/1e4df39a-cc3c-4f45-9466-08a68f8d743c
-- title:
--   Cost of the rotation descriptor for n (κ = 2⁻¹²⁹ constants)
-- statement:
--   **Cost of the rotation descriptor for n**, at the `same-network-129` constants.
--
--   This is `NLogN.KFM.descTrP_cost_n` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFM SE: the axis-rotation descriptor (`TransNeed`)*: `descTr w h bs = [w, h, k, b_0, …, b_{k−1}]` (KFMNeed). In kmain the array has the padded shape
--   `[t_0, …, t_{d−1}]` (`t_j = 2^{h + b_j}`, `h = ℓ − 1`, `b_j = [d' ≤ j]`). After `m` rotations
--   its shape is that list rotated left by `m`, so the descriptor of the next rotation uses the bits
--   `bR n m j = [d' ≤ (j + m) mod d]`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.descTrP_cost_n` (https://prove2.me/theorems/e3fd436a-6351-4d9f-81c9-ccd1fdf58943).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM
open _root_.IntMul
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R129
open _root_.IntMul.OpenAI.RP
open _root_.NLogN.RS
set_option maxHeartbeats 4000000

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM

theorem IntMul.OpenAI.R129.P.NLogN.KFM.descTrP_cost_n (dst rw rm : Fin HS) (hd : TrOk dst rw rm) {n : ℕ} (hn : IntMul.OpenAI.Glue.n0 ≤ n)
    (w m : ℕ) (hwA : w ≤ 2 ^ (2 * bP n + 2)) (hmA : m ≤ 2 ^ (2 * bP n + 2)) (t : IState HS)
    (h : TrRegs t n w m rw rm) :
    (descTrP dst rw rm).cost t ≤ 10 ^ 12 * (bP n + 1) ^ 3 := by sorry
