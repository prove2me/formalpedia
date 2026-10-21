-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFL_lem13_il
-- name    : IntMul.OpenAI.R129.P.NLogN.KFL.lem13_il
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:26:33.635131+00:00
-- url     : https://prove2.me/theorems/1a487f97-e416-4fe5-b72b-88c601eb5213
-- title:
--   Lemma 13 in IL (the corrected statement of KFH_WIP.lem13_iruns, see KFL_WIP): records of R Gaussian… (κ = 2⁻¹²⁹ constants)
-- statement:
--   **Lemma 13 in IL (the corrected statement of KFH_WIP.lem13_iruns, see KFL_WIP): records of R Gaussian…**, at the `same-network-129` constants.
--
--   This is `NLogN.KFL.lem13_il` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFL §18: Lemma 13 in IL*: `lem13_il` (the corrected statement of `KFH_WIP.lem13_iruns`, see `KFL_WIP`): integers → bits
--   (`toBitsI`), the slot canonicalisation by at most two Lemma-12 swaps (`swSeq (preL px py)`), the
--   packed lines (`linesI`), the guard-set correction (`corrI`), the last selected bit (`xorStep`),
--   the inverse swaps and bits → integers (`fromBitsI`).  The composite is `permRecs (rowAddAddr …)`
--   (`bits_permRecs`, `pipeline_rixT`, `Fpp_conj`); the cost is of the form (19) with
--   `τ = 1 - 2^{-42}`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFL.lem13_il` (https://prove2.me/theorems/08e54490-4249-466f-b702-3bd659e0fdff).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open _root_.NLogN hiding P1
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFL hiding LinesOK SwOK coreCost
open _root_.IntMul.OpenAI.R129.P.NLogN.KFL
open _root_.IntMul
open _root_.NLogN.RS
open _root_.NLogN.KIL hiding Bits Cfg FR St aE cBr cMv cRot cStep negP outR padL rV
open _root_.NLogN.KFD
open _root_.NLogN.KFB hiding c1 cPass cZ mvL permL permP rP
open _root_.NLogN.KFH
open _root_.AModel hiding hdPos
open _root_.Butterfly hiding Op

open _root_.NLogN hiding P1
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFL hiding LinesOK SwOK coreCost
open _root_.IntMul.OpenAI.R129.P.NLogN.KFL

theorem IntMul.OpenAI.R129.P.NLogN.KFL.lem13_il :
    ∃ (code : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Fin 3 → Fin 3 → IStmt HS 1) (Kc : ℝ), 0 < Kc ∧
    ∀ {I : List Sym} (N0 N1 N2 N3 K f ρ R w : ℕ) (px py : Fin 3), px ≠ py → 6 ≤ K → ρ < K →
      1 ≤ f → 1 ≤ N0 → 1 ≤ N1 → 1 ≤ N2 → 1 ≤ N3 → 1 ≤ R →
      ∀ (s : IState HS) (g : Fin HS → List ℤ) (zs : List GI) (l : List ℤ),
      g 0 = gflat zs ++ l → zs.length = vol (rect N0 N1 N2 N3 (f * K)) * R → NLogN.KFB.GB w zs →
      ∃ c, IRuns I l12prog (code N0 N1 N2 N3 K f ρ R w px py) (encK s g)
          (encK s (Function.update g 0 (gflat (permRecs (rect N0 N1 N2 N3 (f * K))
            (rowAddAddr K ρ f px py) R zs) ++ l))) c ∧
        (c : ℝ) ≤ Kc * ((zs.length : ℝ) * (w + 1) * (((f * K : ℕ) : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ 42) + 1) +
          (vol (rect N0 N1 N2 N3 (f * K)) : ℝ) * ((zsz (2 * zs.length * (w + 1) : ℤ) : ℝ) + 1) ^ 3 +
          min 1 (80 * ((f : ℝ) - 1) * 2⁻¹ ^ K) * (vol (rect N0 N1 N2 N3 (f * K)) : ℝ) *
            ((zsz (2 * zs.length * (w + 1) : ℤ) : ℝ) + 1) * ((R : ℝ) * (w + 1) +
              (zsz (2 * zs.length * (w + 1) : ℤ) : ℝ) + 1)) := by sorry
