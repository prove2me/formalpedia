-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFY_trBlk_all
-- name    : IntMul.OpenAI.R129.P.NLogN.KFY.trBlk_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:50.931992+00:00
-- url     : https://prove2.me/theorems/38f05a53-22cd-4b0e-a576-be74d2a49286
-- title:
--   trBlk_all (KFY 6: generic combinators for the line passes) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **trBlk_all (KFY 6: generic combinators for the line passes)**, at the `same-network-129` constants.
--
--   This is `NLogN.KFY.trBlk_all` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFY 6: generic combinators for the line passes*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFY.trBlk_all` (https://prove2.me/theorems/b762b66d-4434-4e44-8178-d8abd5ef714f).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN TrHyp ZN axA axB bN fsA fsB mN mainA mainB mmN overN progA progB srcsN tN trBlk trBound trC trPrc ΦN
open _root_.IntMul.OpenAI.R129.P.NLogN.KFY
open _root_.IntMul
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DE DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bitE bsN cLineU cPhiU chirpGN dS descChirpN descLineN descPhiN dpN fmB gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm liftL lineG mN muN parC parQV phiG prodN pushL sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R129

open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN TrHyp ZN axA axB bN fsA fsB mN mainA mainB mmN overN progA progB srcsN tN trBlk trBound trC trPrc ΦN
open _root_.IntMul.OpenAI.R129.P.NLogN.KFY

theorem IntMul.OpenAI.R129.P.NLogN.KFY.trBlk_all (M : MulSpec) (X : Fin HS) (Kc : ℝ) (rw rm : Fin HS) (hd : TrOk X rw rm)
    (hX0 : X ≠ 0) {n : ℕ} (hn : IntMul.OpenAI.Glue.n0 ≤ n) (w m : ℕ) (t : IState HS) (h : TrRegs t n w m rw rm)
    (zs : List KFB.GI) (l : List Item) (h0 : t.G 0 = ints (KFB.gflat zs) ++ l)
    (hz : zs.length = AModel.vol (shPad (ℓP n - 1) (IntMul.OpenAI.R129.P.NLogN.KFM.bsN n m))) (hB : KFB.GB w zs)
    (hh : 1 ≤ ℓP n - 1) (hbs : IntMul.OpenAI.R129.P.NLogN.KFM.bsN n m ≠ []) :
    (trBlk X Kc rw rm).run t = t.upd 0 (ints (KFB.gflat (IntMul.HvdH.Ref.transposeL
        ((shPad (ℓP n - 1) (IntMul.OpenAI.R129.P.NLogN.KFM.bsN n m)).headD 1) (AModel.vol (shPad (ℓP n - 1) (IntMul.OpenAI.R129.P.NLogN.KFM.bsN n m)).tail) zs))
        ++ l) ∧
      (trBlk X Kc rw rm).ok M t ∧
      (trBlk X Kc rw rm).cost M t = 1 + ((descTrP X rw rm).cost (t.upd X (.mark :: t.G X)) +
        (⌈trBound Kc w (ℓP n - 1) (IntMul.OpenAI.R129.P.NLogN.KFM.bsN n m).length
          (AModel.vol (shPad (ℓP n - 1) (IntMul.OpenAI.R129.P.NLogN.KFM.bsN n m)))⌉₊ + trOver w (ℓP n - 1) (IntMul.OpenAI.R129.P.NLogN.KFM.bsN n m).length)) := by sorry
