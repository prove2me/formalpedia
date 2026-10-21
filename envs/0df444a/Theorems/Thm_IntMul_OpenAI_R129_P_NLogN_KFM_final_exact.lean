-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFM_final_exact
-- name    : IntMul.OpenAI.R129.P.NLogN.KFM.final_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:02.418678+00:00
-- url     : https://prove2.me/theorems/2f4c81d5-d669-47d8-87f1-951454f92ea2
-- title:
--   §9.6 exactness in the form of chain_close (κ = 2⁻¹²⁹ constants)
-- statement:
--   **§9.6 exactness in the form of chain_close**, at the `same-network-129` constants.
--
--   This is `NLogN.KFM.final_exact` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFM 14: the exact side of the error chain*: The exact maps of §9.4–9.7 as `LinC` / `BilC` instances, and the identities `chain_close` needs.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.final_exact` (https://prove2.me/theorems/d5ee4f7f-3a33-4ebf-9e24-c61eb304426c).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM
open Complex
open _root_.IntMul.OpenAI.RT
open _root_.IntMul.OpenAI.RC
variable {d : ℕ}
variable {D : ℕ}

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM

theorem IntMul.OpenAI.R129.P.NLogN.KFM.final_exact (s t : Fin d → ℕ) [∀ i, NeZero (s i)] (hcop : ∀ i, Nat.Coprime (s i) (t i))
    (b : ℕ) (ubar vbar : ((i : Fin d) → ZMod (s i)) → ℂ) (j : (i : Fin d) → ZMod (s i)) :
    (2 : ℂ) ^ (2 * b + 4) * (∏ i, (s i : ℂ)) * ((∏ i, (s i : ℂ)) *
      cnj (Rperm s t (dftM s (cnj (Rperm s t (dftM s (fun k => (2 : ℂ)⁻¹ ^ (b + 2) * ubar k)) *
        Rperm s t (dftM s (fun k => (2 : ℂ)⁻¹ ^ (b + 2) * vbar k)))))) j) = cconv s ubar vbar j := by sorry
