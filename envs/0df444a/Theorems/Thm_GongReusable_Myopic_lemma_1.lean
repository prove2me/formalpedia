-- Prove2me | Theorems.Thm_GongReusable_Myopic_lemma_1
-- name    : GongReusable.Myopic.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:28:11.993004+00:00
-- url     : https://prove2.me/theorems/74cf967d-b00c-4b7c-89ea-7b7421bd2d85
-- title:
--   Lemma 1 — validity of the queue coupling
-- statement:
--   For every valid unit-capacity instance, fixed finite arrival sequence, measurable myopic tie rule and nonanticipating competitor, the source FIFO construction supplies the competitor with fresh product-specific usage laws. At each arrival t and product j, for every measurable event E in its own preceding history and current offer, and every measurable duration set B,
--
--   $$\Pr(E,\ j_t^*=j,\ d_t^*\in B)=\Pr(E,\ j_t^*=j)F_j(B).$$
--
--   Consequently the successive rental durations have the stated conditional i.i.d. interpretation up to the finite horizon. The statement also asserts equality of the competitor's entire terminal-history marginal with its standalone operational law. The policies never inspect coupling queues. The independence is relative to the competitor's own past, not the joint history in which ALG may already have observed a queued sample.
--
--   Differences from the source:
--   - encoding: products numbered 1 through n and arrivals 1 through T → an arbitrary finite product type and arrivals indexed by Fin T from zero; reason: relabeling changes neither the model nor the arrival order
--   - generalization: positive product counts, horizons and prices in the unit-capacity model → empty product sets, zero horizons and zero mean fees are also allowed; reason: the nondegenerate source instances are all included; the added cases use rejection or zero revenue
--   - encoding: arbitrary arrival spacing and usage cdfs → nondecreasing nonnegative real epochs and Borel probability measures on extended nonnegative durations; reason: a finite time translation makes every finite arrival sequence nonnegative; zero and infinite durations are represented without discretization
--   - reading: the source does not specify the exact reveal time of a duration or simultaneous-event order → a sampled duration is observed after allocation, and returns at an epoch precede the next ordered offer; reason: this fixes observation and endpoint conventions without revealing future rental draws
--   - encoding: feasible history-dependent assortment policies and implicit no-sale option → measurable decision functions with fresh uniform seeds, empty-offer rejection and a fixed unused history tail; reason: finite-action kernels have this representation; sanitizing infeasible proposals to rejection leaves all feasible behavior representable
--   - encoding: finite expected rental fees and expected cumulative revenue → measurable integrable real rental-fee functions, computed nonnegative means and product-measure integrals of conditional assortment rewards; reason: integrability spells out the finite expectations; independent new rental samples identify this objective with expected full actual fees
--   - encoding: the myopic rule chooses an arbitrary maximizing feasible offer → arbitrary measurable tie proposals with a fixed enumerated-maximizer fallback; reason: every measurable maximizing selection is represented; the fallback only completes a rule that did not propose a maximizer
--   - generalization: the coupled policy is named OPT → any admissible nonanticipating competitor may be coupled; reason: the fresh-law assertion is independent of revenue optimality and includes every optimal policy
--   - encoding: i.i.d. usage times whenever OPT selects a product → measurable-event conditional factorization at every arrival and product, together with the terminal-history marginal equality; reason: the stopped rental sequence must retain its own-past conditional laws; no conditioning on the entire coupled history is imposed
--   - reading: FIFO insertion and extraction when both policies rent at the same arrival → ALG inserts before the competitor extracts; reason: the source construction lists these operations in that order and this fixes simultaneous-event semantics
-- source:
--   Gong, Goyal, Iyengar, Simchi-Levi, Udwani and Wang, Online Assortment Optimization with Reusable Resources, https://doi.org/10.1287/mnsc.2021.4134, supplied manuscript (SSRN 3334789 footers; journal pagination and revision year unverified), Lemma 1, printed p. 12 / PDF p. 12

import Definitions.Def_GongReusable_Myopic_Coupling

open MeasureTheory

namespace GongReusable.Myopic

theorem lemma_1 {P Z : Type} [Fintype P] {T : ℕ}
    (M : Model P Z) (hM : Valid M) (unit : ∀ j, M.capacity j = 1)
    (x : Arrivals Z T) (tie π : Policy P) :
    FreshOptDurations M x tie π ∧
      (jointLaw M T).map (fun w => (coupledRun M x tie π w T).2.1) =
        (tapeLaw M T).map (fun w => run M x (offer M π) w T) := by sorry

end GongReusable.Myopic
