-- Prove2me | Theorems.Thm_MultiThinkCoT_proposition_A_3
-- name    : MultiThinkCoT.proposition_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:40:29.947294+00:00
-- url     : https://prove2.me/theorems/4fbd9c7c-5662-4673-a971-83f505aff88e
-- title:
--   Proposition A.3 — realizable uniform convergence (Fundamental Theorem of Statistical Learning)
-- statement:
--   There is a universal constant $c>0$ such that the following holds. Let $X$ be a measurable space, $D$ a probability measure on $X$, and $H$ a class of measurable functions $X\to\{0,1\}$ that is pointwise separable, with $\mathrm{VCdim}(H)=v<\infty$, and let $h^\star\in H$. For all $\varepsilon,\delta\in(0,1)$ and every sample size
--
--   $$
--   m\ \ge\ c\,\frac{v\log(2/\varepsilon)+\log(1/\delta)}{\varepsilon},
--   $$
--
--   with probability at least $1-\delta$ over $x^{(1)},\dots,x^{(m)}\sim_{\mathrm{iid}}D$, every $\hat h\in H$ with $\hat h(x^{(i)})=h^\star(x^{(i)})$ for all $i$ satisfies $L_{D,h^\star}(\hat h)=\Pr_{x\sim D}[\hat h(x)\neq h^\star(x)]\le\varepsilon$.
--
--   This is the realizable uniform-convergence bound behind every sample-size estimate of the paper (Proposition 6.2, Lemmas F.1, F.2, F.4).
--
--   **Formalization Note** The failure event is "some $h\in H$ agrees with $h^\star$ on the sample and has error $>\varepsilon$", bounded in outer $D^{m}$-measure. Pointwise separability means that a countable subclass approximates every member pointwise. Together with measurability of the members, it is the standing measurability assumption of the textbook result the paper cites ([SSBD14, Thm 6.8]). Both hold for every class on a countable domain with the discrete σ-algebra, which is the case used in this mission. $\log$ is natural. VC dimension is that of `UnderstandingML.vcDim`.
--
--   Differences from the source:
--   - reading: any domain X and any distribution D over X → a measurable space X with a probability measure D; members of H measurable and H pointwise separable; reason: the measurability standing in the cited [SSBD14, Thm 6.8]; without it the uniform statement fails for some classes (Durst–Dudley); on countable domains, the paper's use, both conditions hold for every class
--   - reading: for any consistent ĥ (from Consistent_H(S)) → uniform over all such predictors: the outer probability that some consistent member has error > ε is at most the stated failure probability; reason: the rule may return any consistent member; the guarantee must hold for whichever is returned
--   - encoding: VCdim(H) < ∞ and the sample complexity m(ε, δ) ≤ c(VCdim(H) log(2/ε) + log(1/δ))/ε → vcDim H = v with v : ℕ, and the guarantee for every m ≥ c(v log(2/ε) + log(1/δ))/ε; reason: the same statement with the finite VC dimension named
--   - encoding: ε, δ unrestricted in the statement → ε, δ ∈ (0, 1); reason: the paper's learning parameters range over (0, 1) (Definition 6.2)
--   - encoding: any domain X → X : Type (universe 0); reason: universe level only
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), Appendix A, Proposition A.3, p.35 (PDF p.35)

import Mathlib
import Definitions.Def_UnderstandingML_VC

open MeasureTheory

namespace MultiThinkCoT

/-- **Proposition A.3 (The Fundamental Theorem of Statistical Learning)**, p.35 (PDF p.35).
N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…).

There is a universal constant `c > 0` such that for any domain `X`, any class `H ⊆ {0,1}^X` with
`VCdim(H) = v < ∞`, any distribution `D` over `X` and any `h⋆ ∈ H`: for every `ε, δ ∈ (0,1)` and
every `m ≥ c (v log(2/ε) + log(1/δ))/ε`, with probability at least `1 − δ` over
`x(1), …, x(m) ∼iid D`, every `ĥ ∈ H` consistent with `(x(i), h⋆(x(i)))_{i ≤ m}` has
`L_{D,h⋆}(ĥ) ≤ ε`.

**Formalization Note.**
* "Any consistent `ĥ`" is read uniformly: the failure event is "some `h ∈ H` agrees with `h⋆` on
  the sample and has error `> ε`", and its (outer) `D^m`-measure is at most `δ`.
* "Any domain `X`" is a measurable space with a probability measure `D`; the members of `H` are
  measurable and `H` is pointwise separable (`UnderstandingML.PointwiseSeparable`), the standing
  measurability assumption of the cited [SSBD14, Thm 6.8] (Remark 3.1 there). Without such an
  assumption the uniform statement is false for some classes (Durst and Dudley 1981). On a
  countable domain with the discrete σ-algebra both conditions hold for every class.
* `log` is the natural logarithm; `VCdim` is `UnderstandingML.vcDim` (Definition 6.4).
* `X` ranges over `Type` (universe 0).
-/
theorem proposition_A_3 :
    ∃ c : ℝ, 0 < c ∧
    ∀ {X : Type} [MeasurableSpace X] (H : Set (X → Bool)), (∀ h ∈ H, Measurable h) →
      UnderstandingML.PointwiseSeparable H →
      ∀ v : ℕ, UnderstandingML.vcDim H = v →
      ∀ (D : Measure X) [IsProbabilityMeasure D] (hstar : X → Bool), hstar ∈ H →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∀ m : ℕ, c * ((v : ℝ) * Real.log (2 / ε) + Real.log (1 / δ)) / ε ≤ m →
      Measure.pi (fun _ : Fin m => D)
        {xs | ∃ h ∈ H, (∀ i, h (xs i) = hstar (xs i)) ∧ ε < (D {x | h x ≠ hstar x}).toReal}
        ≤ ENNReal.ofReal δ := by sorry

end MultiThinkCoT
