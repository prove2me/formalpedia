-- Prove2me | Theorems.Thm_HiddenCorr_ERM_lemma_6
-- name    : HiddenCorr.ERM.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:35:23.202116+00:00
-- url     : https://prove2.me/theorems/b2070f52-a919-4975-a86a-c048331cc456
-- title:
--   Lemma 6 — $\hat{\mathfrak R}^{\mathrm{multi}}_X(H)\le\sqrt{2\log S_H(n)}\le C\sqrt{d\log(nk)}$ for one-hot classes of Natarajan dimension $d$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $k\ge2$ and let $H$ be a class of hypotheses with values in $\{e_1,\dots,e_k\}$ (equivalently $[k]$) of finite Natarajan dimension $d\ge1$, and let $S_H(n)$ be its growth function (Eq. (50)). For every sample $X=(X_1,\dots,X_n)$,
--   $$\hat{\mathfrak R}^{\mathrm{multi}}_X(H)\le\sqrt{2\log S_H(n)}\le C\sqrt{d\log(nk)}.$$
--
--   The first inequality is a finite-class bound over the $S_H(n)$ label patterns; the second uses the multiclass counting bound $S_H(n)\le n^dk^{2d}$ (Eq. (51)). Together with Theorem 10 it gives Theorem 11.
--
--   Differences from the source:
--   - encoding: Y = [k] ≅ {e_1, …, e_k}, hypotheses with values in {e_1, …, e_k} → labels and hypotheses Fin k-valued; one-hot vectors onehot r = e_r in the losses and pseudo-labels; reason: same objects
--   - encoding: H has (finite) Natarajan dimension d → MulticlassDS.NatGap.natarajanDim H = (d : ℕ∞); reason: published Natarajan dimension (sequences with f(i) ≠ g(i)); same value as for sets
--   - encoding: E_ε over independent Rademacher signs, conditional on the sample; complexities possibly infinite → uniform average over all sign vectors (finite sum / 2^n); R̂_X, R̂^vec_X valued in [0, ∞] (ℝ≥0∞); reason: same quantity; ℝ≥0∞ keeps an unbounded class's +∞ value
--   - encoding: H is a nonempty class → no separate nonemptiness hypothesis; reason: dimension d ≥ 1 already forces H ≠ ∅ (the empty class has dimension 0), so the hypothesis would be redundant (trap 36)
--   - encoding: R̂^multi real → radMulti valued in EReal; the first inequality compares in EReal; reason: R̂^multi is defined in EReal (see the Complexity definition)
-- source:
--   Chen, Gentile, Kaplan, Koren, Supervised Learning with Hidden Correspondences, STOC 2027 submission (manuscript sha256 d0029978…), p. 32, Lemma 6 (with Eqs. (50)–(51), p. 31; proof p. 65)

import Mathlib
import Definitions.Def_MulticlassDS_NatGap_Dimensions
import Definitions.Def_HiddenCorr_ERM_Complexity

universe u

namespace HiddenCorr.ERM

/-- **Lemma 6**, p. 32 (with Eqs. (50)–(51), p. 31). There is an absolute constant `C > 0` such that
for every `k ≥ 2`, every class `H` of hypotheses `X → [k]` (used as one-hot predictors
`x ↦ e_{h(x)}`) of finite Natarajan dimension `d ≥ 1`, every `n` and every sample
`X = (X₁, …, Xₙ)`: `R̂^multi_X(H) ≤ √(2 log S_H(n)) ≤ C √(d log(nk))`. -/
theorem lemma_6 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {𝒳 : Type u} (k : ℕ), 2 ≤ k → ∀ (H : Set (𝒳 → Fin k)) (d : ℕ), 1 ≤ d →
        MulticlassDS.NatGap.natarajanDim H = d →
        ∀ (n : ℕ) (X : Fin n → 𝒳),
          radMulti X ((fun h x => onehot (h x)) '' H) ≤
              ((Real.sqrt (2 * Real.log (growthFn H n)) : ℝ) : EReal) ∧
            Real.sqrt (2 * Real.log (growthFn H n)) ≤
              C * Real.sqrt (d * Real.log ((n : ℝ) * k)) := by sorry

end HiddenCorr.ERM
