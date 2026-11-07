-- Prove2me | Theorems.Thm_MixScale_lemma_F_6
-- name    : MixScale.lemma_F_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:11:54.717963+00:00
-- url     : https://prove2.me/theorems/ece0e819-e47a-4a1c-89f2-6407c60753ab
-- title:
--   Lemma F.6, p.40 — weighted finite-difference bound
-- statement:
--   Under Definition F.1 with integer $m$, the mixtures $P_\pm$ of the alternatives (84) satisfy
--
--   $$\chi^2(P_+\|P_-)\le Ct^2\Psi_{q,\alpha}(\gamma),\qquad0<\gamma\le c^*,\ 0<t\le1/4,$$
--
--   where $\Psi_{q,\alpha}(\gamma)=\gamma^{E_{q,\alpha}}/\ell_q(\gamma)$ and the constants do not depend on $\gamma,t$.
--
--   Combined with Lemma H.4 at $t=2\varepsilon$, this gives the free-weight lower bound.
--
--   Differences from the source:
--   - encoding: P_± the models in (84) → mixture laws for any component laws of the two tuples; reason: unique by uniqueness of characteristic functions
--   - encoding: Definition F.1 (L¹ derivative, ∂_s^j ĥ_v, continuous representatives, a.e. meaning at infinite-density points) → ∃ m, M_der; L¹ difference-quotient limit written with lower integrals; derivatives within {|s| ≥ 1}, assumed C^{M_der} there; h_v^{(m)} of an ∃-quantified representative C^m off zero; density f real valued; reason: these are the printed conditions; f(0) does not matter and no extra smoothness is added
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), Lemma F.6, p.40 (PDF p.42); (84), p.40; (72), p.35

import Mathlib
import Definitions.Def_MixScale_Regular
import Definitions.Def_MixScale_HardModels
import Definitions.Def_MixScale_Estimator

namespace MixScale

/-- **Lemma F.6** (Weighted finite-difference bound).

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*, STOC
2027 submission manuscript (sha256 5277f95e…7c6c), Lemma F.6, p.40 (PDF p.42), with (84), (72).

**Formalization Note.** `P_±` are the mixture laws of `binomModel` for any component laws of the two
tuples (unique by characteristic functions). `C, c∗` are chosen before `γ, t`. -/
theorem lemma_F_6 (S : ProfileSpec) (m Mder : ℕ) (hS : IsRegularProfileAt S m Mder) :
    ∃ C cstar : ℝ, 0 < C ∧ 0 < cstar ∧
      ∀ γ t : ℝ, 0 < γ → γ ≤ cstar → 0 < t → t ≤ 1 / 4 →
      ∀ Pp Pm : Fin (m + 1) → MeasureTheory.Measure (Vec 1),
        IsCompFamily S.χ (binomModel S.q m γ t true) Pp →
        IsCompFamily S.χ (binomModel S.q m γ t false) Pm →
        chiSq (mixLaw (binomModel S.q m γ t true) Pp) (mixLaw (binomModel S.q m γ t false) Pm) ≤
          ENNReal.ofReal (C * t ^ 2 * PsiQA S.q S.α γ) := by sorry

end MixScale
