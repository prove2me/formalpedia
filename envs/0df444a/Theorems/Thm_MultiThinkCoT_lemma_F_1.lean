-- Prove2me | Theorems.Thm_MultiThinkCoT_lemma_F_1
-- name    : MultiThinkCoT.lemma_F_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:43:43.319587+00:00
-- url     : https://prove2.me/theorems/70b8a470-66c0-4b3d-8534-67bb71bcb28b
-- title:
--   Lemma F.1 — generator chosen after the samples
-- statement:
--   There is a universal constant $c>0$ such that for any base class $\mathcal F$, thinking length $T$, domain $\mathcal X$, distribution $\mathcal D$ over $\mathcal X$, target $h^\star\in\mathcal F^{\mathrm{e2e}\text{-}T}$, $\varepsilon,\delta\in(0,1)$ and sample size
--
--   $$
--   m\ \ge\ c\,\frac{\min\{\log|\mathcal F|,\ \mathrm{VCdim}(\mathcal F^{\mathrm{e2e}\text{-}T})\log(2/\varepsilon)\}+\log\delta^{-1}}{\varepsilon},
--   $$
--
--   with probability at least $1-\delta$ over $x^{(1)},\dots,x^{(m)}\sim_{\mathrm{iid}}\mathcal D$ the following holds simultaneously for every generator $f^\star\in\mathcal F$ with $f^{\star\,\mathrm{e2e}\text{-}T}\equiv h^\star$, which may be selected after the sample is drawn: every $\hat f\in\mathcal F$ whose CoTs agree with those of $f^\star$ on all $x^{(i)}$ satisfies $L_{\mathcal D,h^\star}(\hat f^{\mathrm{e2e}\text{-}T})\le\varepsilon$.
--
--   This is the guarantee that survives an adversary choosing the source after seeing the requested examples, which Lemma F.2 needs.
--
--   **Formalization Note** Both "for every $f^\star$" and "every consistent $\hat f$" are inside the probability. The relation $\equiv$ means agreement at every point of $\mathcal X$. The $\log|\mathcal F|$ branch applies only to finite $\mathcal F$. Natural logarithms; $\mathcal D$ is a probability mass function.
--
--   Differences from the source:
--   - reading: a predictor ĥ returned by (Consistent_CoT), simultaneously for every f⋆ selected after sampling → uniform over all such predictors: the outer probability that some consistent member has error > ε is at most the stated failure probability; reason: the rule may return any consistent member; the guarantee must hold for whichever is returned
--   - reading: f⋆^{e2e-T} ≡ h⋆ → f⋆^{e2e-T}(x) = h⋆(x) for every x ∈ X; reason: ≡ is identity of functions on the domain
--   - encoding: m ≥ c(min{log|F|, ·} + log δ⁻¹)/ε → the disjunction of the two thresholds; the log|F| branch only for finite F (|F| = ncard F), the VC branch only for finite VC dimension; reason: m ≥ c(min{A,B}+β)/ε iff one of the two thresholds is met; log|F| = ∞ for infinite F
--   - encoding: a distribution D ∈ ∆(X) on X ⊆ {0,1}* → D : PMF X; reason: X is countable, so every distribution on it is a probability mass function
--   - encoding: ε (and δ) unquantified in the lemma → ε, δ ∈ (0, 1); reason: the paper's accuracy and confidence parameters range over (0, 1) (Definition 6.2, Theorem 7); for ε ≥ 1 or δ ≥ 1 the conclusion holds trivially, since every error is at most 1
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), Appendix F, Lemma F.1, p.53 (PDF p.53)

import Mathlib
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_MultiThinkCoT_e2eClass
import Definitions.Def_MultiThinkCoT_endToEndError

namespace MultiThinkCoT

/-- **Lemma F.1 (Generator chosen after samples)**, p.53 (PDF p.53).
N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…).

There is a universal `c > 0` such that for any base class `F`, thinking length `T`, domain `X`,
adversary `(D, h⋆)` with `h⋆ ∈ F^{e2e-T}`, `ε, δ ∈ (0,1)` and sample size
`m ≥ c (min{log |F|, VCdim(F^{e2e-T}) log(2/ε)} + log δ⁻¹)/ε`, with probability at least `1 − δ`
over `S_e2e` the following holds simultaneously for every generator `f⋆ ∈ F` with
`f⋆^{e2e-T} ≡ h⋆` (selected after sampling): every predictor returned by (Consistent_CoT) on
`S_CoT = {(x(i), f⋆^{CoT-T}(x(i)))}` has `L_{D,h⋆} ≤ ε`.

**Formalization Note.**
* Both "for every `f⋆`" and "every returned predictor" are inside the probability: the failure
  event is "some `f⋆ ∈ F` realizing `h⋆` on all of `X` and some `f ∈ F` with the same CoTs as `f⋆`
  on the sample have `L_{D,h⋆}(f^{e2e-T}) > ε`".
* `f⋆^{e2e-T} ≡ h⋆` is agreement at every point of `X`.
* The `min` is the disjunction of the two thresholds; `log |F|` only for finite `F`; natural log;
  `D` is a `PMF`.
-/
theorem lemma_F_1 :
    ∃ c : ℝ, 0 < c ∧
    ∀ (F : Set Gen) (T : ℕ) (X : Set (List Bool)) (D : PMF X) (hstar : X → Bool),
      hstar ∈ e2eClass F T X →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∀ m : ℕ,
      ((F.Finite ∧ c * (Real.log F.ncard + Real.log (1 / δ)) / ε ≤ m) ∨
          (∃ v : ℕ, UnderstandingML.vcDim (e2eClass F T X) = v ∧
            c * ((v : ℝ) * Real.log (2 / ε) + Real.log (1 / δ)) / ε ≤ m)) →
      (iidSample D m).toOuterMeasure
        {xs | ∃ fstar ∈ F, (∀ x : X, e2e fstar T x = hstar x) ∧
          ∃ f ∈ F, (∀ i, cot f T (xs i) = cot fstar T (xs i)) ∧
            ε < endToEndError D hstar (fun x => e2e f T x)} ≤ ENNReal.ofReal δ := by sorry

end MultiThinkCoT
