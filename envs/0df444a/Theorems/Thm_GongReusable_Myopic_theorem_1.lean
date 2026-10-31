-- Prove2me | Theorems.Thm_GongReusable_Myopic_theorem_1
-- name    : GongReusable.Myopic.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:26:29.303134+00:00
-- url     : https://prove2.me/theorems/90f07a25-5575-4cfd-9919-a970632b039b
-- title:
--   Theorem 1 — the myopic one-half guarantee as printed
-- statement:
--   Suppose products have arbitrary finite reusable capacities, arbitrary product-only i.i.d. usage distributions, and measurable integrable duration-dependent rental fees with nonnegative finite means. Customer choice models satisfy the source's product regularity assumption. The feasible family contains rejection and is otherwise unrestricted. For every fixed finite sequence of customer types and arrival epochs, and every measurable maximizing myopic tie rule, the printed theorem asserts
--
--   $$J(\mathrm{ALG})\ge \frac12\,\mathrm{OPT}.$$
--
--   The clairvoyant benchmark may use the entire fixed future input and all duration laws, but cannot see future random choices or durations. The myopic decision maximizes current expected fee over physically available feasible offers. Both objectives count full fees from rentals started within the horizon, even when return or collection occurs later. The exact one-half constant and arbitrary capacities are retained. No downward-closure assumption is added. The source-domain counterexample is recorded separately in INSIGHTS.yaml; the target remains the printed claim.
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
-- source:
--   Gong, Goyal, Iyengar, Simchi-Levi, Udwani and Wang, Online Assortment Optimization with Reusable Resources, https://doi.org/10.1287/mnsc.2021.4134, supplied manuscript (SSRN 3334789 footers; journal pagination and revision year unverified), Theorem 1, printed p. 11 / PDF p. 11

import Definitions.Def_GongReusable_Myopic_Process

namespace GongReusable.Myopic

theorem theorem_1 {P Z : Type} [Fintype P] {T : ℕ}
    (M : Model P Z) (hM : Valid M) (x : Arrivals Z T) (tie : Policy P) :
    (1 / 2 : ℝ) * optimalValue M x ≤ myopicValue M x tie := by sorry

end GongReusable.Myopic
