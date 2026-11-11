-- Prove2me | Theorems.Thm_HiddenCorr_ERM_lemma_5
-- name    : HiddenCorr.ERM.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:35:37.193237+00:00
-- url     : https://prove2.me/theorems/a99b3baa-1afa-4246-821c-1375f849fc8e
-- title:
--   Lemma 5 — the coefficient-normalized complexity of a VC class is at most $C\sqrt{d+1}$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $H$ be a nonempty class of $\{0,1\}$-valued functions on $\mathcal X$ with VC dimension $d\ge0$. Then for every $n$ and every sample $x=(x_1,\dots,x_n)\in\mathcal X^n$,
--   $$\hat{\mathfrak R}_x(H)\le C\sqrt{d+1}.$$
--
--   It is the weighted counterpart of the bound $C\sqrt{d/n}$ on the Rademacher complexity of a VC class, uniform in the sample size, and is what makes the binary guarantee free of $\log n$ factors.
--
--   Differences from the source:
--   - encoding: Y = {0, 1}, hypotheses h : X → {0, 1} → labels and hypotheses Bool-valued; the real value b2r b ∈ {0, 1} enters the pseudo-label risk; reason: same objects
--   - encoding: H has VC dimension d → NatureSLT.GrowthFunction.vcDim of the family (h : ↥H) ↦ h equals (d : ℕ∞); reason: published VC dimension; finite d as printed
--   - encoding: E_ε over independent Rademacher signs, conditional on the sample; complexities possibly infinite → uniform average over all sign vectors (finite sum / 2^n); R̂_X, R̂^vec_X valued in [0, ∞] (ℝ≥0∞); reason: same quantity; ℝ≥0∞ keeps an unbounded class's +∞ value
-- source:
--   Chen, Gentile, Kaplan, Koren, Supervised Learning with Hidden Correspondences, STOC 2027 submission (manuscript sha256 d0029978…), p. 28, Lemma 5 (proof p. 29)

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_HiddenCorr_ERM_Complexity

open scoped ENNReal

universe u

namespace HiddenCorr.ERM

/-- **Lemma 5** (complexity of VC classes), p. 28. There is an absolute constant `C > 0` such that
for every nonempty class `H` of `{0, 1}`-valued functions with VC dimension `d ≥ 0` (finite), every
`n` and every sample `x = (x₁, …, xₙ) ∈ Xⁿ`, `R̂_x(H) ≤ C √(d + 1)`. -/
theorem lemma_5 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {𝒳 : Type u} (H : Set (𝒳 → Bool)), H.Nonempty →
        ∀ d : ℕ, NatureSLT.GrowthFunction.vcDim (fun h : H => (h : 𝒳 → Bool)) = d →
        ∀ (n : ℕ) (x : Fin n → 𝒳),
          radX x ((fun h y => b2r (h y)) '' H) ≤ ENNReal.ofReal (C * Real.sqrt ((d : ℝ) + 1)) := by sorry

end HiddenCorr.ERM
