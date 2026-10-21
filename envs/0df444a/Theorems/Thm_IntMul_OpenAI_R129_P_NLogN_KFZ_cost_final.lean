-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFZ_cost_final
-- name    : IntMul.OpenAI.R129.P.NLogN.KFZ.cost_final
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:28:06.795917+00:00
-- url     : https://prove2.me/theorems/5c6ba123-6e15-4bf0-8978-beff0e4c89c4
-- title:
--   cost_final (KFZ CostR: the chirp procedure cost against `cLineU`) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **cost_final (KFZ CostR: the chirp procedure cost against `cLineU`)**, at the `same-network-129` constants.
--
--   This is `NLogN.KFZ.cost_final` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFZ CostR: the chirp procedure cost against `cLineU`*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFZ.cost_final` (https://prove2.me/theorems/822b1d57-159b-405d-b86d-278e8de2bea5).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open _root_.NLogN hiding St T1 T2 T3 T4 T5 T6 T7 tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFZ hiding BN ChirpNeedR bitN bsN hN length_bsN length_ssN ssN σN
open _root_.IntMul.OpenAI.R129.P.NLogN.KFZ
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE cBody negP outR padL pushF pushes
open _root_.NLogN.KFB hiding permL permP qA qT
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DE DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bitE bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN eB eN fmB gapR gconj kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm liftL lineG muN parC parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD sumB tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R129
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R129
attribute [local irreducible] fmA Cfm
variable {n D : ℕ} (hn : n0 ≤ n) (hD : dP n = D + 1)
include hn hD

open _root_.NLogN hiding St T1 T2 T3 T4 T5 T6 T7 tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFZ hiding BN ChirpNeedR bitN bsN hN length_bsN length_ssN ssN σN
open _root_.IntMul.OpenAI.R129.P.NLogN.KFZ

theorem IntMul.OpenAI.R129.P.NLogN.KFZ.cost_final (C18 : ℝ) (hC18 : 0 ≤ C18) (A18 c18 : ℕ)
    (hc : (c18 : ℝ) ≤ C18 * (((tsN n).prod * IntMul.OpenAI.R129.rP n * (pP n + 3) : ℕ) : ℝ) *
      Ncost (6 * (lg n : ℝ)) (IntMul.OpenAI.R129.dP n) (KP n) (ℓP n) (αP n) *
      (Real.log (6 * (lg n : ℝ)) + 1) ^ A18) :
    ((c18 + NLogN.KFZ.cBody (IntMul.OpenAI.R129.P.NLogN.KFZ.BN n) (IntMul.OpenAI.R129.P.NLogN.KFZ.BN n) (bP n) (desc18 (pP n) (ℓP n) (KP n) (tsN n)).length (pP n) (IntMul.OpenAI.R129.P.NLogN.KFZ.hN n)
      D (σN n) (sBD n D) (tBD n D) + 2 : ℕ) : ℝ) ≤ (2 * C18 + Kc) * cLineU n (A18 + 2) := by sorry
