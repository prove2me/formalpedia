-- Prove2me | Theorems.Thm_GeoRobustLearn_lemma_4_2
-- name    : GeoRobustLearn.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:21.253185+00:00
-- url     : https://prove2.me/theorems/ae8a5acd-4e07-46dc-b714-37a65a977ad5
-- title:
--   Lemma 4.2 — $m_V(r)-m_V(-r)\le O(Kr)$ for $V=T_sB_f$
-- statement:
--   There is a constant $C>0$ such that for every $f\in\mathcal C_K$, every $s\in(0,1]$ and every radius $r\ge0$, with $V=T_sB_f$ and $m_V(a)=\mathbb E_{x\sim\gamma}[V(x,a)]$,
--
--   $$m_V(r)-m_V(-r)\le CKr.$$
--
--   Together with Lemma 4.1 this shows that the smoothed offset lift satisfies the expected signed width constraint of the convex program.
--
--   Differences from the source:
--   - encoding: O(Kr) → C·K·r with C > 0 chosen before d, K, f, s, r; reason: the meaning of O(·)
--   - reading: r (unconstrained in the statement) → 0 ≤ r; reason: r is the radius of §4–§6; the claim is about a nonnegative radius
--   - encoding: ℝ^{d+1} ∋ (x, a), T_s, F^{≤k} → Space (d+1) with the offset as last coordinate; the published ou s and truncation k; reason: Lean representation; same objects
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Lemma 4.2, p.18 (PDF p.18)

import Definitions.Def_GeoRobustLearn_BoundaryVolume
import Definitions.Def_GeoRobustLearn_OffsetLift

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-- **Lemma 4.2** (Smoothing preserves the expected signed width bound), p.18.

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…).

There is a constant `C` such that for every `f ∈ C_K`, `s ∈ (0, 1]` and radius `r ≥ 0`, with
`V = T_s B_f` and `m_V(a) = E_{x∼γ}[V(x, a)]`: `m_V(r) − m_V(−r) ≤ C K r`.

**Formalization Note.** `O(Kr)` is `C K r` with `C` chosen before `d`, `K`, `f`, `s`, `r`. `m_V` is
`offsetMean` (a Bochner integral of the bounded continuous function `V`). The signed distance is
extended-valued (`sdist`), so for `f ≡ 1` the lift is `≡ 1` and both sides vanish. -/
theorem lemma_4_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (K s r : ℝ) (f : Space d → ℝ),
        InCK K f → 0 < s → s ≤ 1 → 0 ≤ r →
        offsetMean (ou s (offsetLift f)) r - offsetMean (ou s (offsetLift f)) (-r) ≤
          C * K * r := by sorry

end GeoRobustLearn
