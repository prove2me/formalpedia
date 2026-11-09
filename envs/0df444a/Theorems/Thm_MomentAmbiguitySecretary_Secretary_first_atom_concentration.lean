-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_first_atom_concentration
-- name    : MomentAmbiguitySecretary.Secretary.first_atom_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:20.137194+00:00
-- url     : https://prove2.me/theorems/057f688d-8644-4502-9681-8d8c9efb9260
-- title:
--   Corollary 6.1 — uniform first-atom concentration
-- statement:
--   Fix an integer $N\ge2$. For the distributions of Theorem 3.2, with integer base $B\ge2$,
--
--   $$\min_{0\le h<N}\mu_h(\{B^h\})\longrightarrow1\qquad(B\longrightarrow\infty).$$
--
--   The limit is uniform over the finitely many residues for each fixed $N$. It places no simultaneous growth condition on $N$.
--
--   Differences from the source:
--   - encoding: minimum of atom probabilities for integer bases B at least two → finite minimum of real conversions of atom measures along all natural bases; reason: the conversions are finite probabilities for every B at least two, and finitely many initial bases do not affect the limit
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied preprint, Corollary 6.1, PDF/printed p.15, SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Separator

open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal

namespace MomentAmbiguitySecretary.Secretary

/-- Corollary 6.1, pinned preprint PDF/printed p.15.
The integer base tends to infinity with N fixed; initial B < 2 are irrelevant. -/
theorem first_atom_concentration (N : ℕ) (hN : 2 ≤ N) :
    Tendsto (fun B : ℕ => minimumFirstAtom B N) atTop (𝓝 1) := by sorry

end MomentAmbiguitySecretary.Secretary
