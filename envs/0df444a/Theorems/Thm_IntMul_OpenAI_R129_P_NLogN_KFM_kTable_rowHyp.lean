-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFM_kTable_rowHyp
-- name    : IntMul.OpenAI.R129.P.NLogN.KFM.kTable_rowHyp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:26:42.561871+00:00
-- url     : https://prove2.me/theorems/963cd9f3-939c-4bd9-82b9-67e58183ad08
-- title:
--   Row additions in the merged table (Lemma 13 via KFL, relabelled) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **Row additions in the merged table (Lemma 13 via KFL, relabelled)**, at the `same-network-129` constants.
--
--   This is `NLogN.KFM.kTable_rowHyp` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFM 7: one procedure table for Lemma 12 / Prop 14 and the FM multiplier*: Procedure tables are merged by renaming procedure indices (`IStmt.ren id g`, nlogn `HRen`).
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.kTable_rowHyp` (https://prove2.me/theorems/7066c200-7e97-4f99-87ea-45bc77552092).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM
open Complex
open _root_.IntMul
open _root_.NLogN.RS
open _root_.AModel hiding hdPos
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFD
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.NLogN.KFG hiding cPair imE mulB reE tsE
open _root_.NLogN.KFH
open _root_.NLogN.KFN hiding cMv pcs τ50
open _root_.IntMul.OpenAI.R129.P.NLogN.KFN
open _root_.P8Lift
open _root_.Butterfly hiding Op
variable {E : ℕ}

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM

theorem IntMul.OpenAI.R129.P.NLogN.KFM.kTable_rowHyp (ext : Fin E → IStmt HS (7 + E)) :
    ∃ Kc : ℝ, 0 < Kc ∧ ∀ (Isym : List Sym) {K r Z : ℕ}, 6 ≤ K → 1 ≤ r →
      80 * Z * (Z + 2) ≤ 2 ^ K →
      RowHyp Isym (kTable ext) K (100 ^ 3) r Z (KFR.PsiR r Z) (Kc * (K + 2) + 1) τ50 ∧
        0 ≤ Kc * (K + 2) + 1 ∧ Monotone (KFR.PsiR r Z) ∧ ∀ v, Z + 2 ≤ KFR.PsiR r Z v := by sorry
