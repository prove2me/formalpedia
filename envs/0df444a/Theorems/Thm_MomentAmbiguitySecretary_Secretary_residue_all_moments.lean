-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_residue_all_moments
-- name    : MomentAmbiguitySecretary.Secretary.residue_all_moments
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:18.317126+00:00
-- url     : https://prove2.me/theorems/6289a049-db8e-4d44-9569-7f80cfee57cf
-- title:
--   Lemma 8.9 — all moments are finite and equal
-- statement:
--   Fix integers $B,N\ge2$, residues $0\le h,h'<N$ and an integer $t\ge0$. For the concrete residue measures, both powers are integrable and
--
--   $$\int x^t\,d\mu_h(x)=\int x^t\,d\mu_{h'}(x)<\infty.$$
--
--   This identifies the full moment information of every member of the family, including order zero.
--
--   Differences from the source:
--   - encoding: nonnegative distributions and finite real moments → measures on the nonnegative real subtype with explicit Integrable conclusions; reason: the subtype represents exactly the source domain and integrability records finiteness without default-zero integrals
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied preprint, Lemma 8.9, PDF/printed p.33, SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Separator

open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal

namespace MomentAmbiguitySecretary.Secretary

/-- Lemma 8.9, pinned preprint PDF/printed p.33. -/
theorem residue_all_moments (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N)
    (h h' : Fin N) (t : ℕ) :
    Integrable (fun x : ℝ≥0 => (x : ℝ) ^ t) (residueMeasure B N h.val) ∧
    Integrable (fun x : ℝ≥0 => (x : ℝ) ^ t) (residueMeasure B N h'.val) ∧
    (∫ x : ℝ≥0, (x : ℝ) ^ t ∂residueMeasure B N h.val) =
      ∫ x : ℝ≥0, (x : ℝ) ^ t ∂residueMeasure B N h'.val := by sorry

end MomentAmbiguitySecretary.Secretary
