-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFY_prod_tB
-- name    : IntMul.OpenAI.R154.P.NLogN.KFY.prod_tB
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-20T03:21:54.225953+00:00
-- url     : https://prove2.me/theorems/3be53031-5243-4def-b9e1-2d77bde4a7bf
-- title:
--   prod_tB (KFY 11: size facts of the padded box) (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **prod_tB (KFY 11: size facts of the padded box)**, at the `frozen-154` constants.
--
--   This is `NLogN.KFY.prod_tB` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFY 11: size facts of the padded box*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFY.prod_tB` (https://prove2.me/theorems/f48ec170-1fe1-43f4-859a-dba041f6ede8).

import Definitions.Def_IntMul_OpenAI_R154_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN ZN bN fsA fsB mN mainA mainB mmN overN srcsN tN ΦN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY
open _root_.IntMul
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RP
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DE DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bitE bsN cLineU chirpGN dS descChirpN descLineN descPhiN dpN fmB gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm liftL lineG mN muN parC parQV prodN pushL sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN ZN bN fsA fsB mN mainA mainB mmN overN srcsN tN ΦN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY

theorem IntMul.OpenAI.R154.P.NLogN.KFY.prod_tB {n : ℕ} (hn : IntMul.OpenAI.Glue.n0 ≤ n) : (List.ofFn (IntMul.OpenAI.R154.P.NLogN.KFM.tB n)).prod = 2 ^ IntMul.OpenAI.Glue.LP n := by sorry
