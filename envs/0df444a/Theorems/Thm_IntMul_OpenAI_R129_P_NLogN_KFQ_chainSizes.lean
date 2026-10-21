-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFQ_chainSizes
-- name    : IntMul.OpenAI.R129.P.NLogN.KFQ.chainSizes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:26:45.874402+00:00
-- url     : https://prove2.me/theorems/79f8abf4-3b6f-4309-a77f-3963199ec663
-- title:
--   ChainSizes holds (with n₂ = 0) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **ChainSizes holds (with n₂ = 0)**, at the `same-network-129` constants.
--
--   This is `NLogN.KFQ.chainSizes` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFQ: proof of `NLogN.KFM.ChainSizes`*: For `n ≥ n₀` and `dP n = D + 1`:
--   * `tBD_eq`: `t_i = 2^{axExp L d i}`, hence `∏ t_i = T` (`prod_tBD`) and
--     `(∏_{i<D} t_i) · r = T` (`prod_init`);
--   * `win`: the source windows `(4d−2)t_i < 4d s_i ≤ (4d−1)t_i`, `s_i` odd;
--   * `chainSizes : ChainSizes` (with `n₂ = 0`), from `params_ok`, `L_facts`, `setup_facts`,
--     `src_facts`, `srcS_ok_n` and the abstract lemmas of `KFQArith`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFQ.chainSizes` (https://prove2.me/theorems/c8a1aa50-b6d3-4988-a4dc-ffd4a32fe6bc).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open _root_.NLogN
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.IntMul
open _root_.IntMul.HvdH
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R129
open _root_.IntMul.OpenAI.RP
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DE DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bitE bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN fmB gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm liftL lineG muN parC parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM
set_option maxHeartbeats 1000000

open _root_.NLogN
open _root_.IntMul.OpenAI.R129.P.NLogN

theorem IntMul.OpenAI.R129.P.NLogN.KFQ.chainSizes : ChainSizes := by sorry
