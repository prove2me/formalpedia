-- Prove2me | Theorems.Thm_MixScale_lemma_H_6
-- name    : MixScale.lemma_H_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:13:02.499933+00:00
-- url     : https://prove2.me/theorems/aa2405e4-ce1b-498d-88ac-645c9fcbbabc
-- title:
--   Lemma H.6, p.54 — full testing integral for equal weights
-- statement:
--   Under Definition F.1 with integer $m$, the mixtures $P_\pm$ of the alternatives (108) satisfy, for a constant $c^*>0$ depending only on the fixed profile certificate,
--
--   $$\chi^2(P_+\|P_-)\le Ct^2\frac{\gamma^{2q-\min(q,1)}}{\ell_q(\gamma)},\qquad0<\gamma\le c^*,\ 0<t\le1/4,$$
--
--   including the critical case $q=1$.
--
--   Combined with Lemma H.4 at $t=2\varepsilon$, this gives the equal-weight lower bound.
--
--   Differences from the source:
--   - encoding: P_± for the alternatives in (108) → mixture laws for any component laws of the two tuples; reason: unique by uniqueness of characteristic functions
--   - encoding: Definition F.1 (L¹ derivative, ∂_s^j ĥ_v, continuous representatives, a.e. meaning at infinite-density points) → ∃ m, M_der; L¹ difference-quotient limit written with lower integrals; derivatives within {|s| ≥ 1}, assumed C^{M_der} there; h_v^{(m)} of an ∃-quantified representative C^m off zero; density f real valued; reason: these are the printed conditions; f(0) does not matter and no extra smoothness is added
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), Lemma H.6, p.54 (PDF p.56); (108), p.53

import Mathlib
import Definitions.Def_MixScale_Regular
import Definitions.Def_MixScale_HardModels
import Definitions.Def_MixScale_Estimator

namespace MixScale

/-- **Lemma H.6** (Full testing integral for equal weights).

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*, STOC
2027 submission manuscript (sha256 5277f95e…7c6c), Lemma H.6, p.54 (PDF p.56), with (108), p.53.

**Formalization Note.** `P_±` are the mixture laws of `ptmModel` for any component laws of the two
tuples. `γ^{2q − min(q,1)} = γ^{E_eq}`; the case `q = 1` is covered by `ℓ_q`. -/
theorem lemma_H_6 (S : ProfileSpec) (m Mder : ℕ) (hS : IsRegularProfileAt S m Mder) :
    ∃ C cstar : ℝ, 0 < C ∧ 0 < cstar ∧
      ∀ γ t : ℝ, 0 < γ → γ ≤ cstar → 0 < t → t ≤ 1 / 4 →
      ∀ Pp Pm : Fin (2 ^ m) → MeasureTheory.Measure (Vec 1),
        IsCompFamily S.χ (ptmModel m γ t true) Pp →
        IsCompFamily S.χ (ptmModel m γ t false) Pm →
        chiSq (mixLaw (ptmModel m γ t true) Pp) (mixLaw (ptmModel m γ t false) Pm) ≤
          ENNReal.ofReal (C * t ^ 2 * (γ ^ (2 * S.q - min S.q 1) / ellq S.q γ)) := by sorry

end MixScale
