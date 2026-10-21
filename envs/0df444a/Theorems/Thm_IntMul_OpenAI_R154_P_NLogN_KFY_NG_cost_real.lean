-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFY_NG_cost_real
-- name    : IntMul.OpenAI.R154.P.NLogN.KFY.NG.cost_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T03:18:41.870802+00:00
-- url     : https://prove2.me/theorems/3ce459bd-4fe8-4e28-81a1-893e722fb230
-- title:
--   The pass cost against cLineU n 6 (κ = 2⁻¹⁵⁴ constants)
-- statement:
--   **The pass cost against cLineU n 6**, at the `frozen-154` constants.
--
--   This is `NLogN.KFY.NG.cost_real` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged) with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R154`, and every constant-dependent name lives under `IntMul.OpenAI.R154.P`.
--
--   **Context.** The lemma belongs to the part *KFY 20: the cost of the two passes against `cLineU n 6`*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFY.NG.cost_real` (https://prove2.me/theorems/a49c7bf9-609a-432e-8228-ad911ad1b005).

import Definitions.Def_IntMul_OpenAI_R154_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN ZN bN fsA fsB mN mainA mainB mmN overN srcsN tN ΦN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY
open _root_.IntMul
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.NLogN.GL hiding imE reE rndE
open _root_.NLogN.AX hiding bN
open _root_.NLogN.Rsp hiding BN KN aE cE kE pSt spSt
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154
attribute [local irreducible] IntMul.OpenAI.R154.dP IntMul.OpenAI.R154.αP IntMul.OpenAI.Glue.bP
  IntMul.OpenAI.Glue.LP IntMul.OpenAI.Glue.ℓP IntMul.OpenAI.Glue.KP cZ ZN overN
variable {n : ℕ} (h : NG n)
include h
set_option maxHeartbeats 4000000

open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN ZN bN fsA fsB mN mainA mainB mmN overN srcsN tN ΦN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY
open _root_.NLogN.KFY.NG hiding Lb bl casesOn d5 dbig mk nf rec recOn win2 α4
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY.NG

theorem IntMul.OpenAI.R154.P.NLogN.KFY.NG.cost_real (Kc : ℝ) (hK : 0 ≤ Kc) (Cm Mn : ℕ)
    (hm : Mn ≤ Cm * (SN n * αP n) * 2 ^ IntMul.OpenAI.Glue.LP n * ZN n) (c : ℕ)
    (hc : c ≤ IntMul.OpenAI.R154.dP n * (⌈trBound Kc (pP n + 2) (ℓP n - 1) (IntMul.OpenAI.R154.dP n) (2 ^ IntMul.OpenAI.Glue.LP n)⌉₊ +
        trOver (pP n + 2) (ℓP n - 1) (IntMul.OpenAI.R154.dP n)) + IntMul.OpenAI.R154.dP n * Mn + (2 * IntMul.OpenAI.R154.dP n + 1) * overN n + 2) :
    (c : ℝ) ≤ (17 * Kc + 1 + (Cm : ℝ) * NLogN.KFY.cZ * 4 * 58 ^ 6) * IntMul.OpenAI.R154.P.NLogN.KFM.cLineU n 6 := by sorry
