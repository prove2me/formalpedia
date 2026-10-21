-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFM_lam_complex_eq
-- name    : IntMul.OpenAI.R129.P.NLogN.KFM.lam_complex_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:09.84167+00:00
-- url     : https://prove2.me/theorems/ed190096-e565-46c8-b404-33d7a2cd32b0
-- title:
--   The recursion exponent is τ50 (κ = 2⁻¹²⁹ constants)
-- statement:
--   **The recursion exponent is τ50**, at the `same-network-129` constants.
--
--   This is `NLogN.KFM.lam_complex_eq` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFM 5: the recursion exponent of `complexIface` is `λ = τ50 = 1 - 2^{-42}`*: `KFN.lam_complex_lt_one` only gives `λ = log_m max(s_c/W_c, m^{τ50}, 1) < 1`.  The machine
--   budget (MACHINE-PLAN.md §5 (C)) needs `λ + c < λ'` with `c = 2^{-56}`, `λ' = 1 - 2^{-54}`.
--   Here: `s_c / W_c ≤ m^{τ50}` (**`sc_div_Wc_le`**), hence `Rb = m^{τ50}` and **`lam_complex_eq`**:
--   `λ = τ50`; **`lam_add_c_lt`**: `λ + 2^{-56} < 1 - 2^{-54}`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.lam_complex_eq` (https://prove2.me/theorems/72f26393-414d-4470-b79b-f00035598ea5).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM
open _root_.NLogN.KFN hiding cMv pcs τ50
open _root_.IntMul.OpenAI.R129.P.NLogN.KFN

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM

theorem IntMul.OpenAI.R129.P.NLogN.KFM.lam_complex_eq :
    Real.logb ((100 ^ 3 : ℕ) : ℝ) (Rb P8Lift.sc P8Lift.Wc (100 ^ 3) τ50) = τ50 := by sorry
