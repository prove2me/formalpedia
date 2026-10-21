-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFY_tB_eq
-- name    : IntMul.OpenAI.R129.P.NLogN.KFY.tB_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:56.646356+00:00
-- url     : https://prove2.me/theorems/9820adff-8b35-44be-83c4-c8771a383cee
-- title:
--   tB_eq (KFY 10: `tensorGo` as an iteration over rotated shapes) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **tB_eq (KFY 10: `tensorGo` as an iteration over rotated shapes)**, at the `same-network-129` constants.
--
--   This is `NLogN.KFY.tB_eq` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFY 10: `tensorGo` as an iteration over rotated shapes*: `stepL R f L`: transpose the head axis of the shape `R` to the end (`transposeL`), apply `f` to
--   the consecutive lines. `iterL dims fs k` applies the steps for the rotations `dims.rotate j`,
--   `j < k`. **`tensorGo_iterL`**: `tensorGo` of the list `(dims_i, fs i)_i` is `iterL dims fs d`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFY.tB_eq` (https://prove2.me/theorems/aac13d06-ad0e-4b10-a969-f5db8e012a48).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN TrHyp ZN axA axB bN fsA fsB mN mainA mainB mmN overN progA progB srcsN tN trBlk trBound trC trPrc ΦN
open _root_.IntMul.OpenAI.R129.P.NLogN.KFY
open _root_.IntMul
open _root_.IntMul.HvdH
open _root_.IntMul.HvdH.Ref hiding bflyB bflyT dcomX dcomY difZ ditZ pmulZ
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DE DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bitE bsN cLineU cPhiU chirpGN dS descChirpN descLineN descPhiN dpN fmB gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm liftL lineG mN muN parC parQV phiG prodN pushL sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R129
open _root_.IntMul.OpenAI.RP
open _root_.NLogN.KFB (GI gflat)

open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN TrHyp ZN axA axB bN fsA fsB mN mainA mainB mmN overN progA progB srcsN tN trBlk trBound trC trPrc ΦN
open _root_.IntMul.OpenAI.R129.P.NLogN.KFY

theorem IntMul.OpenAI.R129.P.NLogN.KFY.tB_eq {n : ℕ} (hn : IntMul.OpenAI.Glue.n0 ≤ n) (j : ℕ) (hj : j < IntMul.OpenAI.R129.dP n) :
    IntMul.OpenAI.R129.P.NLogN.KFM.tB n ⟨j, hj⟩ = 2 ^ (ℓP n - 1 + if dpN n ≤ j then 1 else 0) := by sorry
