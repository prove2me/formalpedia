-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFM_src_atoms
-- name    : IntMul.OpenAI.R129.P.NLogN.KFM.src_atoms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:10.010434+00:00
-- url     : https://prove2.me/theorems/5b6c6170-b335-4d6f-a7d1-f7102a4e5560
-- title:
--   src_atoms (KFM SA: the cost of the source and inverse lists for `n`) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **src_atoms (KFM SA: the cost of the source and inverse lists for `n`)**, at the `same-network-129` constants.
--
--   This is `NLogN.KFM.src_atoms` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFM SA: the cost of the source and inverse lists for `n`*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.src_atoms` (https://prove2.me/theorems/4c02f049-42a1-4e4d-b893-97b4689f06cd).

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
open _root_.IntMul.OpenAI.RP
open _root_.NLogN.RS

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM

theorem IntMul.OpenAI.R129.P.NLogN.KFM.src_atoms {n : ℕ} (hn : IntMul.OpenAI.Glue.n0 ≤ n) :
    let A := 2 ^ (2 * bP n + 2)
    dpN n ≤ A ∧ srcQ (IntMul.OpenAI.R129.dP n) (IntMul.OpenAI.R129.rP n) ≤ A ∧ srcM (IntMul.OpenAI.R129.dP n) (IntMul.OpenAI.R129.rP n) (IntMul.OpenAI.R129.rP n / 2) ≤ A ∧
      srcM (IntMul.OpenAI.R129.dP n) (IntMul.OpenAI.R129.rP n) (IntMul.OpenAI.R129.rP n) ≤ A ∧ IntMul.OpenAI.R129.dP n ≤ A ∧ IntMul.OpenAI.R129.rP n * IntMul.OpenAI.R129.rP n ≤ A := by sorry
