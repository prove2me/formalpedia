-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_robust_secretary_value
-- name    : MomentAmbiguitySecretary.Secretary.robust_secretary_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:16.738725+00:00
-- url     : https://prove2.me/theorems/13b82a18-37ee-45e0-96e6-4ab50de3d4cc
-- title:
--   Theorem 6.1 — exact independent and i.i.d. robust secretary values
-- statement:
--   For every integer horizon $m\ge1$, the optimal robust success probability in the labeled cardinal-value random-order secretary problem under exact full moment disclosure is the exact classical finite-horizon value in both information models:
--
--   $$V_m^{\mathrm{ind}}=s_m\quad\text{and}\quad V_m^{\mathrm{iid}}=s_m.$$
--
--   In the independent model every label may have any nonnegative law with every finite moment. The i.i.d. policy knows identical distribution and receives its common full moment sequence. Each value is the supremum over measurable moment-based randomized nonanticipating policies of the infimum of actual success probabilities over all admissible input laws, with their resulting disclosures. Success means selecting any maximizer, including ties and zero values; no selection fails. The formula is $s_m=\max_{1\le r\le m}p_m(r)$, where $p_m(1)=1/m$ and $p_m(r)=(r-1)m^{-1}\sum_{t=r}^m(t-1)^{-1}$ for $r\ge2$.
--
--   This preserves both optimal-value equalities for every finite horizon, not only the asymptotic constant.
--
--   Differences from the source:
--   - encoding: measurable randomized stopping policies and their robust success values → causal terminal stopping kernels on realizable disclosure spaces and actual product-experiment probabilities; reason: finite-horizon single-choice causal masses have a sequential implementation; separate disclosure types preserve the independent and i.i.d. information models
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied preprint, Theorem 6.1, PDF/printed p.16, SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Values

open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal

namespace MomentAmbiguitySecretary.Secretary

/-- Theorem 6.1, pinned preprint PDF/printed pp.16–17.
Both complete optimal robust equalities, for every positive integer horizon. -/
theorem robust_secretary_value (m : ℕ) (hm : 1 ≤ m) :
    independentValue m = classicalValue m ∧ iidValue m = classicalValue m := by sorry

end MomentAmbiguitySecretary.Secretary
