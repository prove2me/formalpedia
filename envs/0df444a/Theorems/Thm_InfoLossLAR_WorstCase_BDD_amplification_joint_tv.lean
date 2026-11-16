-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_BDD_amplification_joint_tv
-- name    : InfoLossLAR.WorstCase.BDD.amplification_joint_tv
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:11:17.106209+00:00
-- url     : https://prove2.me/theorems/a0550236-3107-48c0-94bb-62b620710e77
-- title:
--   Whole-transcript majority amplification with one total-variation error
-- statement:
--   Let $T$ independent ideal trials return complete candidate secrets, with each trial correct with probability at least $3/4$. Let $F$ be any failure event such that failure implies at least $T/2$ of the complete candidates are incorrect. Suppose the law of the actual full $T$-trial transcript is within total variation $\varepsilon$ of the full independent ideal product law. Then
--
--   $$
--   \Pr_{\rm actual}[F]\le (7/8)^T+\varepsilon.
--   $$
--
--   The actual transcript may contain arbitrary correlations. The bound charges total variation once for the whole joint transcript; it assumes neither independence of actual trials nor conditional independence given a shared sample pool. The theorem is useful for amplifying a whole-secret decoder while controlling joint source replacement.
--
--   **Formalization Note.** Finite outcome laws are `AFT.FiniteDist`; `readout` returns complete secrets rather than coordinatewise votes. The predicate `F` may be any decidable event satisfying the stated failure condition.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, §3.2.1, Lemmas 3.6–3.7 (search and amplification). This finite-product exponential-moment bound with explicit whole-joint total variation is an independently proved auxiliary lemma for the formal reduction, not a verbatim lemma of that paper.

import Definitions.Def_InfoLossLAR_LoadedBatchBundle_05
set_option autoImplicit false
open AFT
open scoped BigOperators

theorem InfoLossLAR.WorstCase.BDD.amplification_joint_tv {Outcome Secret : Type*} [Fintype Outcome] [DecidableEq Secret]
    (trials : ℕ) (law : Fin trials → FiniteDist Outcome)
    (readout : Fin trials → Outcome → Secret) (secret : Secret)
    (fail : (Fin trials → Outcome) → Prop) [DecidablePred fail]
    (hsuccess : ∀ i, (3/4 : ℝ) ≤ ∑ x, if readout i x = secret then (law i).weight x else 0)
    (hfail : ∀ outcomes, fail outcomes → trials ≤ 2 *
      (∑ i, if readout i (outcomes i) = secret then 0 else 1))
    (actual : FiniteDist (Fin trials → Outcome)) (jointError : ℝ)
    (hjoint : FiniteDist.TVBound actual (FiniteDist.independent law) jointError) :
    (∑ outcomes, if fail outcomes then actual.weight outcomes else 0) ≤
      (7/8 : ℝ)^trials + jointError := by sorry
