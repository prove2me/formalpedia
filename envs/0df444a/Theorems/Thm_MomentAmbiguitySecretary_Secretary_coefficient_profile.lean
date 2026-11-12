-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_coefficient_profile
-- name    : MomentAmbiguitySecretary.Secretary.coefficient_profile
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:12.855921+00:00
-- url     : https://prove2.me/theorems/804afa43-4fc2-4eff-b8ee-bda3477794a4
-- title:
--   Lemma 8.10 — coefficient bounds and exact equality cases
-- statement:
--   Under the standing assumptions $N,B\ge2$, write $j=L(N-1)+b$, $0\le b<N-1$, and $e(j)=(N-1)L(L-1)/2+Lb$. For every $j\ge0$,
--
--   $$B^{-e(j)}\le w_j\le2^jB^{-e(j)},\qquad j-e(j)\le N-1,$$
--
--   and equality in the last inequality holds if and only if $N-1\le j\le2N-2$.
--
--   The full two-sided estimate and equality characterization quantify the decay of all coefficients.
--
--   Differences from the source:
--   - encoding: integer parameters and the signed difference j-e(j) → natural parameters with the signed difference computed in the integers; reason: nonnegative integer ranges are unchanged and signed subtraction prevents truncation
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied preprint, Lemma 8.10, PDF/printed p.33, SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Separator

open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal

namespace MomentAmbiguitySecretary.Secretary

/-- Lemma 8.10, pinned preprint PDF/printed pp.33–34. The N ≥ 2
standing assumption of §8.2 remains in force; the signed difference is in ℤ. -/
theorem coefficient_profile (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    coefficientProfile B N := by sorry

end MomentAmbiguitySecretary.Secretary
