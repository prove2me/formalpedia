-- Prove2me | Theorems.Thm_GongReusable_Myopic_proposition_1
-- name    : GongReusable.Myopic.proposition_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:27:25.786813+00:00
-- url     : https://prove2.me/theorems/dd4b9730-d6dd-462e-a814-7041a9830ed8
-- title:
--   Proposition 1 — arbitrary-to-unit inventory invariance
-- statement:
--   For every valid reusable-assortment instance, every fixed finite arrival sequence and every measurable myopic tie rule, the labeled-unit transformation preserves both the clairvoyant optimal expected revenue and the expected revenue of the corresponding myopic policy:
--
--   $$\mathrm{OPT}(M,x)=\mathrm{OPT}(M_u,x),\qquad J_M(\mathrm{ALG})=J_{M_u}(\mathrm{ALG}_{\mathrm{lift}}).$$
--
--   The capacities are arbitrary finite integers. Each clone inherits its product's complete duration law and duration-dependent fee. Feasibility is checked through projection, and the least offered clone carries the physical choice probability. The corresponding myopic execution is the explicit lift of the same original selection, not an unrelated maximizing tie rule.
--
--   Differences from the source:
--   - encoding: products numbered 1 through n and arrivals 1 through T → an arbitrary finite product type and arrivals indexed by Fin T from zero; reason: relabeling changes neither the model nor the arrival order
--   - generalization: positive product counts, horizons, capacities and prices in the nondegenerate model → empty product sets, zero horizons, zero capacities and zero mean fees are also allowed; reason: the nondegenerate source instances are all included; the added cases use rejection or zero revenue
--   - encoding: arbitrary arrival spacing and usage cdfs → nondecreasing nonnegative real epochs and Borel probability measures on extended nonnegative durations; reason: a finite time translation makes every finite arrival sequence nonnegative; zero and infinite durations are represented without discretization
--   - reading: the source does not specify the exact reveal time of a duration or simultaneous-event order → a sampled duration is observed after allocation, and returns at an epoch precede the next ordered offer; reason: this fixes observation and endpoint conventions without revealing future rental draws
--   - encoding: feasible history-dependent assortment policies and implicit no-sale option → measurable decision functions with fresh uniform seeds, empty-offer rejection and a fixed unused history tail; reason: finite-action kernels have this representation; sanitizing infeasible proposals to rejection leaves all feasible behavior representable
--   - encoding: finite expected rental fees and expected cumulative revenue → measurable integrable real rental-fee functions, computed nonnegative means and product-measure integrals of conditional assortment rewards; reason: integrability spells out the finite expectations; independent new rental samples identify this objective with expected full actual fees
--   - encoding: the clairvoyant optimal policy knows fixed future inputs but no future realizations → the supremum over the nonempty bounded class of measurable own-history policies; reason: this gives the same optimal value without assuming an optimizer as an extra binder
--   - encoding: the myopic rule chooses an arbitrary maximizing feasible offer → arbitrary measurable tie proposals with a fixed enumerated-maximizer fallback; reason: every measurable maximizing selection is represented; the fallback only completes a rule that did not propose a maximizer
--   - encoding: copy labels 1 through c_j and corresponding myopic executions → labels Fin c_j and the least-available-copy lift of the original myopic rule; reason: the label shift and deterministic choice of available copy preserve the paper transformation and both equality clauses
-- source:
--   Gong, Goyal, Iyengar, Simchi-Levi, Udwani and Wang, Online Assortment Optimization with Reusable Resources, https://doi.org/10.1287/mnsc.2021.4134, supplied manuscript (SSRN 3334789 footers; journal pagination and revision year unverified), Proposition 1, printed p. 10 / PDF p. 10

import Definitions.Def_GongReusable_Myopic_UnitCopies

namespace GongReusable.Myopic

theorem proposition_1 {P Z : Type} [Fintype P] {T : ℕ}
    (M : Model P Z) (hM : Valid M) (x : Arrivals Z T) (tie : Policy P) :
    optimalValue M x = optimalValue (unitModel M) x ∧
      myopicValue M x tie = liftedMyopicValue M x tie := by sorry

end GongReusable.Myopic
