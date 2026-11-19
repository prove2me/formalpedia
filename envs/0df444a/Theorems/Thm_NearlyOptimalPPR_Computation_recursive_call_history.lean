-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_call_history
-- name    : NearlyOptimalPPR.Computation.recursive_call_history
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:10:44.424903+00:00
-- url     : https://prove2.me/theorems/10353fc1-8b42-4f03-b376-960f9235d59f
-- title:
--   Persistent call history and exact event counters
-- statement:
--   Every finite-prefix recursive execution has persistent call information, monotone closed-call records, and fixed parameters throughout the open lifetime of a frame. Its event counters are exact:
--
--   $$F_i(T)=\#\{t<T:\text{a full solve for call }i\text{ occurs at }t\},$$
--
--   $$E_i(T)=\#\{t<T:\text{an episode for call }i\text{ starts at }t\}.$$
--
--   The assertions hold for every finite graph, seed, depth, schedule, and real parameters. Information persistence means a recorded call retains its level, scale, and block size. Fixed frame parameters include its threshold and identifier. No positivity, termination, accuracy, or complexity assumption is needed.
--
--   These operational bookkeeping facts connect the event counts in the finite-prefix proof of Lemma 4.4 to the actual counters of Algorithms 6–9.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Algorithms 6–9 pp.14–22 and finite-prefix bookkeeping in the proof of Lemma 4.4 pp.28–29.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
attribute [local instance] Classical.propDecidable

theorem NearlyOptimalPPR.Computation.recursive_call_history (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n)
    (α q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) :
    (∀ (a b id : ℕ) (info : CallInformation), a ≤ b →
      (recursiveRun m g s α q ℓ schedule a).information id=some info →
      (recursiveRun m g s α q ℓ schedule b).information id=some info) ∧
    (∀ a b : ℕ, a ≤ b →
      (recursiveRun m g s α q ℓ schedule a).closed ⊆ (recursiveRun m g s α q ℓ schedule b).closed) ∧
    (∀ a b j : ℕ, a ≤ b →
      (∀ k, a ≤ k → k < b → j ≤ (recursiveRun m g s α q ℓ schedule k).top) →
      frozenFrame ((recursiveRun m g s α q ℓ schedule b).frames j)=
        frozenFrame ((recursiveRun m g s α q ℓ schedule a).frames j)) ∧
    (∀ T id : ℕ,
      (recursiveRun m g s α q ℓ schedule T).fullSolves id=
        ((Finset.range T).filter (fun k => fullSolveEvent g (recursiveRun m g s α q ℓ schedule k) id)).card ∧
      (recursiveRun m g s α q ℓ schedule T).episodes id=
        ((Finset.range T).filter (fun k => episodeEvent (recursiveRun m g s α q ℓ schedule k) id)).card) := by sorry
