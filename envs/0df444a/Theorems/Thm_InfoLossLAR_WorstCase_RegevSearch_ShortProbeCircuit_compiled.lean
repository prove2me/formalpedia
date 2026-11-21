-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_ShortProbeCircuit_compiled
-- name    : InfoLossLAR.WorstCase.RegevSearch.ShortProbeCircuit.compiled
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T04:42:34.384782+00:00
-- url     : https://prove2.me/theorems/90a61053-ea2d-4c60-91eb-011aa92afec8
-- title:
--   Independent query postprocessing with a product failure bound
-- statement:
--   Let $A$ be a measured quantum circuit family and let $q(w)$ be a finite list of requests determined by a classical input $w$. Suppose a uniform quantum family emits a framed transcript whose readouts have the product Born law of independent executions of $A$ on these requests. For any deterministic polynomial-time function $f$ of $w$ and the list of readouts, there is a uniform measured family $T$ with the following guarantee.
--
--   Fix distinct positions $i_1,\ldots,i_m$ in $q(w)$ and an event $H$ on an individual readout. If the presence of any readout in $H$ prevents the output of $f$ from lying in a loss event $L$, even after appending arbitrary padding, then
--   $$
--   \Pr[T(w)\in L]\leq\prod_{j=1}^m\Pr[A(q(w)_{i_j})\notin H].
--   $$
--   The bound allows arbitrary additional requests outside the chosen positions.
-- source:
--   Derivation for InfoLossLAR.WorstCase.RegevSearch.search_to_dual_candidate_lists, Independent query postprocessing with a product failure bound. https://prove2.me/theorems/98258395-a948-48ad-91ba-ef2767f47f76

import Definitions.Def_InfoLossLAR_LoadedBatchBundle_05
import Definitions.Def_InfoLossLAR_RegevSearch
open QAlgorithms.Complexity InfoLossLAR.WorstCase
open OAI.MetricKMedian.Binary.Automatic
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.ShortProbeCircuit

theorem compiled (A : MFamily) (qs : Str → List Str) (finish : Str × List Str → Str)
    (hf : Poly finish) (ht :
    ∃ F : MFamily, IsMQPT F ∧ ∀ w : Str,
      let requests := qs w
      let width (i : Fin requests.length) :=
        (requests.get i).length + (A.anc (requests.get i).length + 1)
      ∃ padding : ((i : Fin requests.length) → Bits (width i)) → Str,
        ∀ event : Str → Prop, outputProb F w event =
          ∑ xs : (i : Fin requests.length) → Bits (width i),
            let outs := List.ofFn (fun i => List.ofFn fun j =>
              xs i (A.outW (requests.get i).length j))
            if event (padding xs ++ (encS w ++ encL encS outs).reverse)
            then ∏ i, ‖runLayered (A.circ (requests.get i).length)
              (basisInput (toBits (requests.get i))) (xs i)‖^2 else 0) :
    ∃ T : MFamily, IsMQPT T ∧ ∀ w : Str, ∀ n : ℕ,
      ∀ pick : Fin n ↪ Fin (qs w).length,
      ∀ (ok loss : Str → Prop),
      (∀ os tail, (∃ o ∈ os, ok o) → ¬loss (finish (w,os) ++ tail)) →
      outputProb T w loss ≤
        ∏ j, outputProb A ((qs w).get (pick j)) (fun o => ¬ok o) := by sorry

end InfoLossLAR.WorstCase.RegevSearch.ShortProbeCircuit
