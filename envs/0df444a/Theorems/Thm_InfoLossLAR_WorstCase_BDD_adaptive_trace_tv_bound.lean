-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_BDD_adaptive_trace_tv_bound
-- name    : InfoLossLAR.WorstCase.BDD.adaptive_trace_tv_bound
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:26:17.637357+00:00
-- url     : https://prove2.me/theorems/32b2cef4-3812-4cc5-af3d-de9a5e7a09da
-- title:
--   Adaptive BDD transcript failure under one whole-law replacement
-- statement:
--   Let $P$ and $Q$ be probability distributions on the same finite space of complete transcripts, with $\operatorname{TV}(P,Q)\le\delta$. Let $F$ be a failure event, and let $B_i$ be events for finitely many stages $i$ such that every transcript in $F$ lies in at least one $B_i$. If
--
--   $$
--   Q(B_i)\le \varepsilon_i\quad\text{for every }i,
--   $$
--
--   then
--
--   $$
--   P(F)\le\delta+\sum_i\varepsilon_i.
--   $$
--
--   The events $B_i$ may be the first incorrect stage after a correct adaptive prefix. The full actual and reference transcript laws may each have arbitrary dependencies between stages; the total variation hypothesis is on the entire transcript and is charged once. This isolates the probability step used to combine a correct BDD trajectory with a correlated source pool.
--
--   **Formalization Note.** The finite laws and eventwise total-variation bound are the existing platform `AFT.FiniteDist` and `TVBound`; no algorithmic BDD implementation is asserted.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, §3.2.1, especially Lemmas 3.4 and 3.5 (adaptive residue trajectory). This elementary eventwise total-variation and union bound is an explicit formalization aid, not a verbatim result or a BDD construction in the source.

import Definitions.Def_InfoLossLAR_LoadedBatchBundle_05
set_option autoImplicit false
open AFT
open scoped BigOperators

theorem InfoLossLAR.WorstCase.BDD.adaptive_trace_tv_bound {Ω : Type*} [Fintype Ω] (steps : ℕ)
    (actual ideal : FiniteDist Ω) (err : ℝ)
    (htv : FiniteDist.TVBound actual ideal err)
    (bad : Fin steps → Ω → Prop) [∀ i, DecidablePred (bad i)]
    (fail : Ω → Prop) [DecidablePred fail]
    (hfail : ∀ ω, fail ω → ∃ i, bad i ω)
    (bound : Fin steps → ℝ)
    (hstage : ∀ i, (∑ ω, if bad i ω then ideal.weight ω else 0) ≤ bound i) :
    (∑ ω, if fail ω then actual.weight ω else 0) ≤ err + ∑ i, bound i := by sorry
