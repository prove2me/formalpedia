-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFY_passA_all
-- name    : IntMul.OpenAI.R129.P.NLogN.KFY.passA_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:28.45578+00:00
-- url     : https://prove2.me/theorems/f13366a8-17ae-4302-a56e-0dad43b0bdce
-- title:
--   The A pass (κ = 2⁻¹²⁹ constants)
-- statement:
--   **The A pass**, at the `same-network-129` constants.
--
--   This is `NLogN.KFY.passA_all` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFY 16: the `A` pass and the `B₀` pass*: The arrays keep the invariant `length = ∏ t_i`, `DiscL p` (which gives `GB (p + 2)`), using an
--   `M : AxisMaps` (`disc_sapL`, `disc_b0Pad`).
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFY.passA_all` (https://prove2.me/theorems/5d02b9b0-9835-4399-8f01-dcc4ea983715).

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
open _root_.IntMul.HvdH.Ref hiding bflyB bflyT dcomX dcomY difZ ditZ pmulZ
open _root_.NLogN.GL hiding imE reE rndE
open _root_.NLogN.AX hiding bN
open _root_.NLogN.Rsp hiding BN KN aE cE kE pSt spSt
set_option maxHeartbeats 8000000

open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN TrHyp ZN axA axB bN fsA fsB mN mainA mainB mmN overN progA progB srcsN tN trBlk trBound trC trPrc ΦN
open _root_.IntMul.OpenAI.R129.P.NLogN.KFY

theorem IntMul.OpenAI.R129.P.NLogN.KFY.passA_all (M : MulSpec) (X : Fin HS) (Kc : ℝ) (hXok : KFM.TrOk X zw zm) (hX0 : X ≠ 0)
    (hw : cX ∉ (axA X Kc).writes)
    {n : ℕ} (hn : IntMul.OpenAI.Glue.n0 ≤ n) [∀ i, NeZero (IntMul.OpenAI.R129.P.NLogN.KFM.sB n i)] [∀ i, NeZero (IntMul.OpenAI.R129.P.NLogN.KFM.tB n i)]
    (Mx : KFM.AxisMaps (d := IntMul.OpenAI.R129.dP n) (IntMul.OpenAI.Glue.pP n) (IntMul.OpenAI.R129.αP n) (IntMul.OpenAI.R129.P.NLogN.KFM.sB n) (IntMul.OpenAI.R129.P.NLogN.KFM.tB n))
    (s : IState HS) (zs : List KFB.GI) (R0 R : List Item)
    (h0 : s.G 0 = ints (KFB.gflat zs) ++ R0)
    (hD : s.G NLogN.KFY.dS = ints (NLogN.KFY.descL (IntMul.OpenAI.Glue.pP n) (IntMul.OpenAI.R129.αP n) (IntMul.OpenAI.R129.ℓP n - 1) (IntMul.OpenAI.R129.dP n) (IntMul.OpenAI.R129.P.NLogN.KFM.dpN n)
      (srcsN n)) ++ R)
    (hzs : ArrInv n zs)
    (Bo mm Φ Bacc Q Bq : ℕ) (hM : MulBnd M mm Φ)
    (HA : ∀ k < IntMul.OpenAI.R129.dP n, SapHyp (IntMul.OpenAI.Glue.pP n) (IntMul.OpenAI.R129.P.NLogN.KFM.srcN n k) (tN n k) (IntMul.OpenAI.R129.αP n)
      (IntMul.OpenAI.Glue.pP n + 2) Bo mm Bacc Q ∧ TabHyp (IntMul.OpenAI.Glue.pP n) (IntMul.OpenAI.R129.P.NLogN.KFM.srcN n k) (tN n k) (IntMul.OpenAI.R129.αP n) Bq ∧
      AxQA (tN n k) (IntMul.OpenAI.R129.P.NLogN.KFY.mN n k) (IntMul.OpenAI.Glue.pP n + 2) Bo Q)
    (A B : ℕ) (hb : AxBnd n A B) (hWB : zsz (((IntMul.OpenAI.Glue.pP n + 1) * (IntMul.OpenAI.Glue.pP n + 1) * (IntMul.OpenAI.R129.αP n + 1) : ℕ) : ℤ) ≤ B)
    (hlA : IntMul.OpenAI.R129.ℓP n ≤ A) (hdlA : IntMul.OpenAI.R129.dP n * IntMul.OpenAI.R129.ℓP n ≤ A)
    (CA : ℕ) (hCA : ∀ k < IntMul.OpenAI.R129.dP n, axAC Kc n k B 20
        (⌈trBound Kc (IntMul.OpenAI.Glue.pP n + 2) (IntMul.OpenAI.R129.ℓP n - 1) (IntMul.OpenAI.R129.dP n) ((List.ofFn (IntMul.OpenAI.R129.P.NLogN.KFM.tB n)).prod)⌉₊ +
          trOver (IntMul.OpenAI.Glue.pP n + 2) (IntMul.OpenAI.R129.ℓP n - 1) (IntMul.OpenAI.R129.dP n))
        (sapAxCostQ (IntMul.OpenAI.Glue.pP n) (IntMul.OpenAI.R129.P.NLogN.KFM.srcN n k) (tN n k) (IntMul.OpenAI.R129.αP n) (IntMul.OpenAI.R129.P.NLogN.KFY.mN n k) mm Φ Bacc Q Bq) ≤ CA) :
    (progA X Kc).run s = s.upd 0 (ints (KFB.gflat
        (tensorGo (mapsA (IntMul.OpenAI.Glue.pP n) (IntMul.OpenAI.R129.αP n) (IntMul.OpenAI.R129.P.NLogN.KFM.sB n) (IntMul.OpenAI.R129.P.NLogN.KFM.tB n)) (List.ofFn (IntMul.OpenAI.R129.P.NLogN.KFM.tB n)) zs))
        ++ R0) ∧
      (progA X Kc).ok M s ∧
      (progA X Kc).cost M s ≤ passC (IntMul.OpenAI.R129.dP n) B
        ((IntMul.OpenAI.Glue.pP n + 1) * 29 * 10 ^ 7 * (B + 2) ^ 2 + 4 * 10 ^ 7 * (B + 2) ^ 2) CA := by sorry
