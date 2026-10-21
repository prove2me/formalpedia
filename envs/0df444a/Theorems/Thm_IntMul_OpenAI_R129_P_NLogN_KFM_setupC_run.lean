-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFM_setupC_run
-- name    : IntMul.OpenAI.R129.P.NLogN.KFM.setupC_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:26:53.151982+00:00
-- url     : https://prove2.me/theorems/7584ffd0-f9eb-4e74-833f-4ce042637159
-- title:
--   setupC_run (KFM S3: the scalar setup parameters as counts (math side)) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **setupC_run (KFM S3: the scalar setup parameters as counts (math side))**, at the `same-network-129` constants.
--
--   This is `NLogN.KFM.setupC_run` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFM S3: the scalar setup parameters as counts (math side)*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.setupC_run` (https://prove2.me/theorems/2dbcc671-cc66-4bfe-aebb-4d1512541c39).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM
open _root_.IntMul
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R129
open _root_.NLogN.RS
set_option maxHeartbeats 2000000

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM

theorem IntMul.OpenAI.R129.P.NLogN.KFM.setupC_run (n : ℕ) (hn : n0 ≤ n) (s : IState HS) (LD LR : List Item)
    (hD : s.G NLogN.KFM.zD = .int (dP n : ℤ) :: LD) (hR : s.G zR = .int (IntMul.OpenAI.R129.rP n : ℤ) :: LR) :
    setupC.ok s ∧ setupC.run s = ((s.upd zQ (.int (srcQ (dP n) (IntMul.OpenAI.R129.rP n) : ℤ) :: s.G zQ)).upd zMh
      (.int (srcM (dP n) (IntMul.OpenAI.R129.rP n) (IntMul.OpenAI.R129.rP n / 2) : ℤ) :: s.G zMh)).upd zMf
      (.int (srcM (dP n) (IntMul.OpenAI.R129.rP n) (IntMul.OpenAI.R129.rP n) : ℤ) :: s.G zMf) := by sorry
