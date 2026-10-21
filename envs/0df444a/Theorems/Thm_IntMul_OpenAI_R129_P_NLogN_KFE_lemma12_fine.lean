-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFE_lemma12_fine
-- name    : IntMul.OpenAI.R129.P.NLogN.KFE.lemma12_fine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:26:25.650756+00:00
-- url     : https://prove2.me/theorems/a7c9b539-8d55-4da5-b9bd-b9fd5af586ac
-- title:
--   Fine Lemma 12 for the bit network (m = 10⁶, W = W_b, τ = 1 − 2^{−42}): the program l12F q m W_b, run with… (κ = 2⁻¹²⁹ constants)
-- statement:
--   **Fine Lemma 12 for the bit network (m = 10⁶, W = W_b, τ = 1 − 2^{−42}): the program l12F q m W_b, run with…**, at the `same-network-129` constants.
--
--   This is `NLogN.KFE.lemma12_fine` from xuanji's $\kappa = 2^{-182}$ formalization (statement unchanged; the proof of the motif exponent now uses $\log 10^6 < 14$, i.e. $e^{14} > 10^6$, so that $m^{1-2^{-42}} \ge m(1 - 14 \cdot 2^{-42})$ exceeds the rank-sum ratio of the network) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFE: fine Lemma 12, unconditional versions*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFE.lemma12_fine` (https://prove2.me/theorems/8b31b483-0fa7-44bf-b1aa-f1ee85dec977).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open _root_.NLogN
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFE
open Finset
open _root_.IntMul
open _root_.NLogN.RS
open _root_.AModel hiding hdPos
open _root_.AModelL12
open _root_.AModelRat
open _root_.AModelFac
open _root_.NLogN.KIL hiding Cfg FR St aE negP outR padL
open _root_.NLogN.KFD
open _root_.NetProp7

open _root_.NLogN
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFE

theorem IntMul.OpenAI.R129.P.NLogN.KFE.lemma12_fine :
    ∃ T q₀ cE : ℕ, ∀ q, q.Prime → q₀ < q → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (u : ℕ) (Pre G Suf : Shape) (Bb : ℕ), 1 ≤ u →
      (∀ a ∈ Pre, 1 ≤ a) → (∀ a ∈ G, 1 ≤ a) → (∀ a ∈ Suf, 1 ≤ a) →
      zsz ((T * (q ^ 2 * vol (binShape Pre G Suf (2 ^ u)) + 1) ^ 2 : ℕ) : ℤ) ≤ Bb → 1 ≤ Bb →
      ∀ (I : List Sym) (s : IState HS) (F : Fin HS → List ℤ) (xs : List (ZMod 2))
        (LP LG LS LU : List ℤ),
      F kP = (vol Pre : ℤ) :: LP → F kG = (vol G : ℤ) :: LG → F NLogN.KIL.kS = (vol Suf : ℤ) :: LS →
      F aU = (u : ℤ) :: LU → F 0 = enc2 xs →
      F 8 = [] → F 9 = [] → F 10 = [] → F 11 = [] → F 15 = [] → F 20 = [] → F 21 = [] →
      F 23 = [] → F 24 = [] →
      xs.length = vol (binShape Pre G Suf (2 ^ u)) →
      ∃ c : ℕ, IRuns I (progF ((bitQC NetProp7.ind₀).toCircuit 1) (edgeTplQ (bitQC NetProp7.ind₀)))
        (l12F q (100 ^ 3) (Fintype.card (NetScalar.Wr NetProp7.ind₀))) (encK s F)
        (encK s (Function.update F 0 (enc2 (AModel.pull (binShape Pre G Suf (2 ^ u))
          (binShape Pre G Suf (2 ^ u)) (swapPos Pre.length (Pre.length + 1 + G.length)) 0 xs))))
        c ∧
        (c : ℝ) ≤ K * (((vol (binShape Pre G Suf (2 ^ u)) : ℝ) + 1) * (u : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ 42) +
          ((u : ℝ) + 1) ^ cE * ((Bb : ℝ) + 2) ^ 2) := by sorry
