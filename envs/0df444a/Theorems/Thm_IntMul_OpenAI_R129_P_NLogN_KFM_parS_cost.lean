-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFM_parS_cost
-- name    : IntMul.OpenAI.R129.P.NLogN.KFM.parS_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:01.522397+00:00
-- url     : https://prove2.me/theorems/271cb727-b7eb-4678-80ae-501e299714cd
-- title:
--   Sizes of the small values. -/ theorem zszQ {b : ℕ} {z : ℤ} (h : |z| ≤ 2 ^ (b + 1)) : zsz z ≤ 8 * b + 8 :=… (κ = 2⁻¹²⁹ constants)
-- statement:
--   **Sizes of the small values. -/ theorem zszQ {b : ℕ} {z : ℤ} (h : |z| ≤ 2 ^ (b + 1)) : zsz z ≤ 8 * b + 8 :=…**, at the `same-network-129` constants.
--
--   This is `NLogN.KFM.parS_cost` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFM SetC: the cost of the parameter pushes*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.parS_cost` (https://prove2.me/theorems/d8591af4-effc-4d0d-be50-0c758b379606).

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
open _root_.NLogN.RS
set_option maxHeartbeats 4000000

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM

theorem IntMul.OpenAI.R129.P.NLogN.KFM.parS_cost {n : ℕ} (hn : IntMul.OpenAI.Glue.n0 ≤ n) (t : IState HS) (LD LB : List Item)
    (hD : t.G zD = .int (IntMul.OpenAI.R129.dP n : ℤ) :: LD) (hB : t.G NLogN.KFM.zB = .int (bP n : ℤ) :: LB)
    (h : SrcRegs t (dpN n) (srcQ (IntMul.OpenAI.R129.dP n) (IntMul.OpenAI.R129.rP n)) (srcM (IntMul.OpenAI.R129.dP n) (IntMul.OpenAI.R129.rP n) (IntMul.OpenAI.R129.rP n / 2))
      (srcM (IntMul.OpenAI.R129.dP n) (IntMul.OpenAI.R129.rP n) (IntMul.OpenAI.R129.rP n))) :
    parS.cost t ≤ 100 * (10 ^ 7 * (16 * bP n + 17 + 2) ^ 2) * (IntMul.OpenAI.R129.dP n + 2) := by sorry
