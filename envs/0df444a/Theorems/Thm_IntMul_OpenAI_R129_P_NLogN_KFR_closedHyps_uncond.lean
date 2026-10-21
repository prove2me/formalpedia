-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFR_closedHyps_uncond
-- name    : IntMul.OpenAI.R129.P.NLogN.KFR.closedHyps_uncond
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:26:56.295969+00:00
-- url     : https://prove2.me/theorems/8da9fc6a-73e8-40e7-a8ca-9c7980fe91b0
-- title:
--   closedHyps_uncond (Prop 14 row additions, unconditional) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **closedHyps_uncond (Prop 14 row additions, unconditional)**, at the `same-network-129` constants.
--
--   This is `NLogN.KFR.closedHyps_uncond` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *Prop 14 row additions, unconditional*: `KFL.lem13_il` (proved in `KFLMain`) discharges `KFR.Lem13IL`, so the row-addition
--   hypothesis `RowHyp` of `KFN.prop14_il_complex_closed` / `KFM.prop14Ph_complex_closed`
--   holds for the Lemma 12 program table `KFL.l12prog`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFR.closedHyps_uncond` (https://prove2.me/theorems/334b364a-5a99-4a56-b8d9-1b170e6acd9c).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open _root_.NLogN
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFR hiding Lem13Body Lem13IL Lem13ILP bnd
open _root_.IntMul.OpenAI.R129.P.NLogN.KFR
open _root_.IntMul
open _root_.NLogN.RS
open _root_.NLogN.KIL hiding Cfg FR St aE negP outR padL
open _root_.NLogN.KFH
open _root_.NLogN.KFN hiding pcs τ50
open _root_.IntMul.OpenAI.R129.P.NLogN.KFN

open _root_.NLogN
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFR hiding Lem13Body Lem13IL Lem13ILP bnd
open _root_.IntMul.OpenAI.R129.P.NLogN.KFR

theorem IntMul.OpenAI.R129.P.NLogN.KFR.closedHyps_uncond :
    ∃ Kc : ℝ, 0 < Kc ∧ ∀ (Isym : List Sym) {K r Z : ℕ}, 6 ≤ K → 1 ≤ r →
      80 * Z * (Z + 2) ≤ 2 ^ K →
      RowHyp Isym KFL.l12prog K (100 ^ 3) r Z (PsiR r Z) (Kc * (K + 2) + 1) τ50 ∧
        0 ≤ Kc * (K + 2) + 1 ∧ Monotone (PsiR r Z) ∧ ∀ v, Z + 2 ≤ PsiR r Z v := by sorry
