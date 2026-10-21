-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFTop_kappa_of_P14Uat_le
-- name    : IntMul.OpenAI.R129.P.NLogN.KFTop.kappa_of_P14Uat_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:15.366822+00:00
-- url     : https://prove2.me/theorems/1cd0fec7-f8bb-4a61-a40b-e3ff7480b278
-- title:
--   The κ bound, conditional only on uniform Prop 14 at some gate constant A ≤ Wc² (κ = 2⁻¹²⁹ constants)
-- statement:
--   **The κ bound, conditional only on uniform Prop 14 at some gate constant A ≤ Wc²**, at the `same-network-129` constants.
--
--   This is `NLogN.KFTop.kappa_of_P14Uat_le` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *The κ machine: top-level reduction*: `R129.P.MachineGoal` from the remaining uniform interfaces.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFTop.kappa_of_P14Uat_le` (https://prove2.me/theorems/da0317e2-d77d-4aa4-851a-f3d05f24ad04).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open _root_.NLogN
open _root_.IntMul.OpenAI.R129.P.NLogN

open _root_.NLogN
open _root_.IntMul.OpenAI.R129.P.NLogN

theorem IntMul.OpenAI.R129.P.NLogN.KFTop.kappa_of_P14Uat_le (A : ℕ) (HU : IntMul.OpenAI.R129.P.NLogN.KFV.P14Uat A) (hA : A ≤ KFAz.A0) :
    IntMul.OpenAI.R129.P.MachineGoal := by sorry
