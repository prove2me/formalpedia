-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFM_kappa_of_big
-- name    : IntMul.OpenAI.R129.P.NLogN.KFM.kappa_of_big
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:26:51.147904+00:00
-- url     : https://prove2.me/theorems/a5560b8d-659a-4956-aef3-7131d7a57fdc
-- title:
--   The top-level reduction (κ = 2⁻¹²⁹ constants)
-- statement:
--   **The top-level reduction**, at the `same-network-129` constants.
--
--   This is `NLogN.KFM.kappa_of_big` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFM K1: the top level — reading, the small-`n` branch, compilation*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.kappa_of_big` (https://prove2.me/theorems/a817410e-4f48-4193-9797-948cdfaf4e4c).

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
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R129

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM

theorem IntMul.OpenAI.R129.P.NLogN.KFM.kappa_of_big {P : ℕ} (F : Fin P → IStmt HS P) (pM bigE : Fin P) (N₁ : ℕ) (Tb : ℕ → ℕ)
    (hM : ∀ I, MulOK I F pM ⟨fun a b => mulCostH (zsz a + zsz b), fun _ _ => True⟩)
    (hB : BigSpec F bigE N₁ Tb) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (A : ℕ)
    (hT : ∀ n, IntMul.OpenAI.Glue.n0 ≤ n → N₁ ≤ n → (2 * ((Tb n + topOvh n N₁ : ℕ) : ℝ) + 1 : ℝ) ≤
      C₀ * (VP n * Ncost (6 * (IntMul.lg n : ℝ)) (IntMul.OpenAI.R129.dP n) (KP n) (ℓP n) (αP n) *
        (Real.log (6 * (IntMul.lg n : ℝ)) + 1) ^ A + n)) :
    IntMul.OpenAI.R129.P.MachineGoal := by sorry
