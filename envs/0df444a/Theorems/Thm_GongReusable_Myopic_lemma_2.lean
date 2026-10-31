-- Prove2me | Theorems.Thm_GongReusable_Myopic_lemma_2
-- name    : GongReusable.Myopic.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:28:12.686877+00:00
-- url     : https://prove2.me/theorems/44dbc318-b373-400d-b118-74ce2bdb3656
-- title:
--   Lemma 2 — revenue from products unavailable to ALG
-- statement:
--   For every valid unit-capacity instance with arbitrary product-specific usage distributions, every fixed finite arrival sequence, any measurable myopic tie rule and any nonanticipating competitor, under the source's concrete FIFO coupling,
--
--   $$\mathbb E\!\left[\sum_{t=1}^T\sum_{j\in S_t^*\setminus I_t}r_j\phi^{z_t}(j,S_t^*)\right]\le\mathbb E\!\left[\sum_{t=1}^T R(S_t,z_t)\right].$$
--
--   Here I_t is ALG's physical available-product set before the offer, S_t and S_t^* are the actual offers in the two runs, and r_j is the full expected rental fee. Choice probabilities on the left are evaluated at the full competitor offer S_t^*, not its difference with I_t. Regularity and the full model assumptions remain in force; no coupling-validity lemma or revenue inequality is a hypothesis.
--
--   Differences from the source:
--   - encoding: products numbered 1 through n and arrivals 1 through T → an arbitrary finite product type and arrivals indexed by Fin T from zero; reason: relabeling changes neither the model nor the arrival order
--   - generalization: positive product counts, horizons and prices in the unit-capacity model → empty product sets, zero horizons and zero mean fees are also allowed; reason: the nondegenerate source instances are all included; the added cases use rejection or zero revenue
--   - encoding: arbitrary arrival spacing and usage cdfs → nondecreasing nonnegative real epochs and Borel probability measures on extended nonnegative durations; reason: a finite time translation makes every finite arrival sequence nonnegative; zero and infinite durations are represented without discretization
--   - reading: the source does not specify the exact reveal time of a duration or simultaneous-event order → a sampled duration is observed after allocation, and returns at an epoch precede the next ordered offer; reason: this fixes observation and endpoint conventions without revealing future rental draws
--   - encoding: feasible history-dependent assortment policies and implicit no-sale option → measurable decision functions with fresh uniform seeds, empty-offer rejection and a fixed unused history tail; reason: finite-action kernels have this representation; sanitizing infeasible proposals to rejection leaves all feasible behavior representable
--   - encoding: finite expected rental fees and expected cumulative revenue → measurable integrable real rental-fee functions, computed nonnegative means and product-measure integrals of conditional assortment rewards; reason: integrability spells out the finite expectations; independent new rental samples identify this objective with expected full actual fees
--   - encoding: the myopic rule chooses an arbitrary maximizing feasible offer → arbitrary measurable tie proposals with a fixed enumerated-maximizer fallback; reason: every measurable maximizing selection is represented; the fallback only completes a rule that did not propose a maximizer
--   - generalization: the comparator is the clairvoyant optimum OPT → any admissible nonanticipating competitor is allowed; reason: the source charging bound does not use optimality and this includes its full stated comparator
--   - reading: FIFO operations at a shared arrival → ALG inserts before the competitor extracts; reason: this fixes the queue construction consistently with Lemma 1
-- source:
--   Gong, Goyal, Iyengar, Simchi-Levi, Udwani and Wang, Online Assortment Optimization with Reusable Resources, https://doi.org/10.1287/mnsc.2021.4134, supplied manuscript (SSRN 3334789 footers; journal pagination and revision year unverified), Lemma 2, printed p. 12 / PDF p. 12 (proof continues on p. 13)

import Definitions.Def_GongReusable_Myopic_Coupling

open MeasureTheory

namespace GongReusable.Myopic

theorem lemma_2 {P Z : Type} [Fintype P] {T : ℕ}
    (M : Model P Z) (hM : Valid M) (unit : ∀ j, M.capacity j = 1)
    (x : Arrivals Z T) (tie π : Policy P) :
    (∫ w, unavailableRevenue M x tie π w ∂jointLaw M T) ≤
      ∫ w, coupledMyopicRevenue M x tie π w ∂jointLaw M T := by sorry

end GongReusable.Myopic
