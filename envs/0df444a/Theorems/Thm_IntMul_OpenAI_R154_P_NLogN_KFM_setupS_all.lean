-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFM_setupS_all
-- name    : IntMul.OpenAI.R154.P.NLogN.KFM.setupS_all
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-20T03:19:15.045471+00:00
-- url     : https://prove2.me/theorems/df72080b-3cd9-48a4-9ef6-f5afa53a9960
-- title:
--   The scalar setup program: from n on zN and b = lg n on zB, it pushes the §9.2 parameters, in O((lg n)^4) steps (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **The scalar setup program: from n on zN and b = lg n on zB, it pushes the §9.2 parameters, in O((lg n)^4) steps**, at the `frozen-154` constants.
--
--   This is `NLogN.KFM.setupS_all` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFM S4: the cost of the scalar setup program*: For `n ≥ n₀`, with `b = lg n`, every atom the setup expressions read is at most `A = 2^{b+2}`.
--   The expressions have degree at most `8`, so all values have fewer than `B = 8b+17` bits
--   (`KFMSm`). This gives
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.setupS_all` (https://prove2.me/theorems/d4045032-81ea-4eb2-88ef-85b5877c1bb0).

import Definitions.Def_IntMul_OpenAI_R154_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.IntMul
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RP
open _root_.NLogN.RS
set_option maxHeartbeats 4000000

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

theorem IntMul.OpenAI.R154.P.NLogN.KFM.setupS_all (n : ℕ) (hn : n0 ≤ n) (s : IState HS) (LN LB : List Item)
    (hN : s.G zN = .int (n : ℤ) :: LN) (hB : s.G zB = .int (bP n : ℤ) :: LB) :
    setupS.ok s ∧ setupS.run s = setupSt n s ∧
      setupS.cost s ≤ 12 * 10 ^ 15 * (bP n + 1) ^ 4 := by sorry
