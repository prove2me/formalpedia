-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_Supplement_spectral_threshold_private_decisions
-- name    : MinimaxInterventions1429.Separable.Supplement.spectral_threshold_private_decisions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:21:38.083216+00:00
-- url     : https://prove2.me/theorems/f03eec33-6402-4556-9d03-f72aaa7ea376
-- title:
--   Theorem 6.8 — Spectral threshold for reusable private decisions
-- statement:
--   Consider family (4) for an arbitrary public group design. Let $\varepsilon\ge0$, $\delta\in[0,1)$, $0\le\beta<\pi_{\varepsilon,\delta}$, and $\varpi=\sqrt{(\pi-\beta)/(1-\beta)}$. Every full-domain private synopsis simultaneously accurate on bounded separable queries has
--   $$\alpha\ge\min\{\Lambda/8,\varpi\sigma(A)/12\}.$$
--   Accuracy may hold on the entire label domain or only on the balanced class for any maximizing pair $(R,S)$ and any $y^0$. When $N<2$, the empty maximum is zero and whole-domain accuracy is covered. If also $\varepsilon\le1/16$, $\delta\le1/32$, $\beta\le1/3$, then $\varpi\ge1/3$ and $\alpha\ge\min\{\Lambda/8,\sigma(A)/36\}$.
--
--   For every $\varepsilon>0$ the public selection of the three literal mechanisms is pure $\varepsilon$-DP and simultaneously accurate with probability at least $2/3$ at every database for all real separable surcharges, with
--   $$\alpha\le\min\left\{\Lambda,\frac{2\sqrt{\log(6m)/n_{\min}}+\log(6m)/n_{\min}}{\varepsilon},\frac{n_{\rm at}+\sqrt{2n_{\rm at}\log3}+\log3}{\varepsilon n_{\min}}\right\}.$$
--   The individual-noise and atom-count mechanisms each satisfy their displayed bound simultaneously for every real cellwise surcharge as well. The statement includes probability-law, measurability and privacy guarantees for these literal constructions. Natural logarithms are used; overlapping group noises need not be independent.
--
--   Differences from the source:
--   - encoding: spectral lower bounds and three constructive upper mechanisms → a unified accuracy-class quantifier and explicit independent Laplace laws with a public minimum-bound selection; reason: all maximizing pairs and both whole-domain and restricted accuracy are covered; natural logs and all-cellwise upper guarantees are retained
--   - encoding: m and k indexed from 1, with m,k >= 2 → Fin m and Fin k indexed from 0, with explicit nonzero instances and m,k >= 2; reason: source column 1 is Lean column 0; dimensions and closed-simplex boundary instances are preserved
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Theorem 6.8, printed p.23 (PDF p.25)

import Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Groups
set_option autoImplicit false
universe u_spectral_threshold_private_decisions

noncomputable section

namespace MinimaxInterventions1429.Separable.Supplement
open MeasureTheory

theorem spectral_threshold_private_decisions
    {N m : ℕ} [NeZero m] (hm : 2 ≤ m) (d : GroupDesign N m) :
    (∀ (ε δ β α : ℝ), 0 ≤ ε → (0 ≤ δ ∧ δ < 1) →
      (0 ≤ β ∧ β < privacyPi ε δ) → 0 ≤ α →
      ∀ (X : Set (Labels N)),
        (X = Set.univ ∨ ∃ (R : Finset (Fin m)) (S : Finset (Fin N)) (y₀ : Labels N),
          R.Nonempty ∧ 2 ≤ S.card ∧ Even S.card ∧
          restrictedSigma d.matrix R S * Real.sqrt ((S.card : ℝ)/R.card) = spectralSigma d.matrix ∧
          X = balancedClass S y₀) →
        ∀ (Z : Type) [MeasurableSpace Z] (syn : Synopsis Z m 2) (law : Labels N → Measure Z),
          PrivateSynopsis replacement d.table {B | Allowed B} ε δ β α syn law X →
          min (d.lambda/8) (varpi ε δ β*spectralSigma d.matrix/12) ≤ α ∧
          (ε ≤ 1/16 → δ ≤ 1/32 → β ≤ 1/3 →
            1/3 ≤ varpi ε δ β ∧ min (d.lambda/8) (spectralSigma d.matrix/36) ≤ α)) ∧
    (∀ ε : ℝ, 0 < ε →
      ((∀ y, IsProbabilityMeasure (bestUpperLaw d ε y)) ∧
        DifferentiallyPrivate replacement ε 0 (bestUpperLaw d ε) ∧
        (∀ B, Measurable (fun s => (bestUpperDecoder d s B).val)) ∧
        ∀ y, Success (bestUpperLaw d ε y) (1/3)
          (AccurateOn (bestUpperDecoder d) {B | IsSeparable B} (d.table y)
            (min d.lambda (min (individualBound d ε) (atomBound d ε))))) ∧
      ((∀ y, IsProbabilityMeasure (individualRelease d ε y)) ∧
        DifferentiallyPrivate replacement ε 0 (individualRelease d ε) ∧
        (∀ B, Measurable (fun v => (releaseDecoder d v B).val)) ∧
        ∀ y, Success (individualRelease d ε y) (1/3)
          (AccurateOn (releaseDecoder d) Set.univ (d.table y) (individualBound d ε))) ∧
      ((∀ y, IsProbabilityMeasure (atomRelease d ε y)) ∧
        DifferentiallyPrivate replacement ε 0 (atomRelease d ε) ∧
        ∀ y, Success (atomRelease d ε y) (1/3)
          (AccurateOn (releaseDecoder d) Set.univ (d.table y) (atomBound d ε)))) := by sorry

end MinimaxInterventions1429.Separable.Supplement
