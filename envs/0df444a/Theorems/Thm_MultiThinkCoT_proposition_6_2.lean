-- Prove2me | Theorems.Thm_MultiThinkCoT_proposition_6_2
-- name    : MultiThinkCoT.proposition_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:43:28.221205+00:00
-- url     : https://prove2.me/theorems/6509e421-6453-402a-aef4-147bb99ee401
-- title:
--   Proposition 6.2 — sample complexity of the E2E and single-thinker CoT consistent rules
-- statement:
--   There is a universal constant $c>0$ such that for any base class $\mathcal F$, thinking length $T$, domain $\mathcal X$, distribution $\mathcal D$ over $\mathcal X$, target $h^\star\in\mathcal F^{\mathrm{e2e}\text{-}T}$ and $\varepsilon,\delta\in(0,1)$:
--
--   1. **E2E rule.** If
--   $$
--   m\ \ge\ c\,\frac{\min\{\log|\mathcal F|,\ \mathrm{VCdim}(\mathcal F^{\mathrm{e2e}\text{-}T})\log(2/\varepsilon)\}+\log\delta^{-1}}{\varepsilon},
--   $$
--   then with probability at least $1-\delta$ over $x^{(1)},\dots,x^{(m)}\sim_{\mathrm{iid}}\mathcal D$, every $\hat f\in\mathcal F$ with $\hat f^{\mathrm{e2e}\text{-}T}(x^{(i)})=h^\star(x^{(i)})$ for all $i$ has $L_{\mathcal D,h^\star}(\hat f^{\mathrm{e2e}\text{-}T})\le\varepsilon$.
--   2. **CoT rule.** Let $f^\star\in\mathcal F$ be a fixed generator with $f^{\star\,\mathrm{e2e}\text{-}T}=h^\star$ $\mathcal D$-almost surely, chosen before the inputs are sampled. If
--   $$
--   m\ \ge\ c\,\frac{\min\{\log|\mathcal F|,\ \mathrm{VCdim}(\mathcal L^{\mathrm{CoT}\text{-}T}(\mathcal F))\log(2/\varepsilon)\}+\log\delta^{-1}}{\varepsilon},
--   $$
--   then with probability at least $1-\delta$ every $\hat f\in\mathcal F$ with $\hat f^{\mathrm{CoT}\text{-}T}(x^{(i)})=f^{\star\,\mathrm{CoT}\text{-}T}(x^{(i)})$ for all $i$ has $L_{\mathcal D,h^\star}(\hat f^{\mathrm{e2e}\text{-}T})\le\varepsilon$.
--
--   These are the single-source learning guarantees on which the relaxed-protocol analysis of Lemma F.2 rests.
--
--   **Formalization Note** $|\mathcal F|$ is the cardinality of a finite class, and the $\log|\mathcal F|$ branch is absent for infinite $\mathcal F$. Natural logarithms. $\mathcal D$ is a probability mass function. Almost-sure agreement means agreement on the support of $\mathcal D$, as in (4).
--
--   Differences from the source:
--   - reading: the rules Consistent_e2e / Consistent_CoT learn F^{e2e-T} with sample complexity m(ε, δ) (Definition 6.2) → for every m above the threshold, the outer probability that some consistent f ∈ F has L_{D,h⋆}(f^{e2e-T}) > ε is at most δ; reason: the rule may return any consistent member, so the guarantee is uniform over them
--   - encoding: m ≥ c(min{log|F|, ·} + log δ⁻¹)/ε → the disjunction of the two thresholds; the log|F| branch only for finite F (|F| = ncard F), the VC branch only for finite VC dimension; reason: m ≥ c(min{A,B}+β)/ε iff one of the two thresholds is met; log|F| = ∞ for infinite F
--   - reading: a fixed single generator chosen before observing the inputs, realizing h⋆ as in (4) → a fixed f⋆ ∈ F with f⋆^{e2e-T}(x) = h⋆(x) for every x in the support of D, quantified outside the probability; reason: (4) states agreement almost surely for x ∼ D
--   - encoding: a distribution D ∈ ∆(X) on X ⊆ {0,1}* → D : PMF X; reason: X is countable, so every distribution on it is a probability mass function
--   - encoding: VCdim(F^{e2e-T}), VCdim(L^{CoT-T}(F)) → named finite values v, w : ℕ in the VC branch; reason: an infinite VC dimension makes that branch's threshold infinite
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), §6.2, Proposition 6.2, p.18 (PDF p.18)

import Mathlib
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_MultiThinkCoT_e2eClass
import Definitions.Def_MultiThinkCoT_cotLossClass
import Definitions.Def_MultiThinkCoT_endToEndError

namespace MultiThinkCoT

/-- **Proposition 6.2 (Theorems 3.1, 3.2, 3.4 [JVB+25])**, p.18 (PDF p.18).
N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…).

There is a universal `c > 0` such that for any base class `F`, thinking length `T` and domain `X`:

1. the rule (Consistent_e2e) learns `F^{e2e-T}` with sample complexity
   `m(ε, δ) ≤ c (min{log |F|, VCdim(F^{e2e-T}) log(2/ε)} + log δ⁻¹)/ε`;
2. the rule (Consistent_CoT) learns `F^{e2e-T}` under CoT supervision from a fixed single
   generator chosen before the inputs are sampled with sample complexity
   `m(ε, δ) ≤ c (min{log |F|, VCdim(L^{CoT-T}(F)) log(2/ε)} + log δ⁻¹)/ε`.

"Learns with sample complexity" is Definition 6.2: for every `ε, δ ∈ (0,1)`, every choice of the
adversary (`D`, `h⋆ ∈ F^{e2e-T}`, and in part 2 the generator `f⋆ ∈ F` realizing `h⋆` as in (4))
and every `m ≥ m(ε, δ)`, with probability at least `1 − δ` the returned predictor has
`L_{D,h⋆} ≤ ε`.

**Formalization Note.**
* Each rule may return any consistent member; the statement is uniform over all of them: the
  failure event is "some consistent `f ∈ F` has `L_{D,h⋆}(f^{e2e-T}) > ε`".
* `m ≥ c (min{A, B} + log δ⁻¹)/ε` is the disjunction of `m ≥ c (A + log δ⁻¹)/ε` and
  `m ≥ c (B + log δ⁻¹)/ε`; `log |F|` is available only for finite `F` (`|F| = ncard F`), and the VC
  branch only when the VC dimension is finite.
* In part 2, `f⋆` is fixed before sampling and realizes `h⋆` `D`-almost surely (eq. (4)):
  `f⋆^{e2e-T}(x) = h⋆(x)` on the support of `D`. CoT supervision gives `z(i) = f⋆^{CoT-T}(x(i))`.
* `log` is the natural logarithm; `D` is a `PMF` on the countable domain; VC dimensions are
  `UnderstandingML.vcDim`, of `F^{e2e-T}` over `X` and of `L^{CoT-T}(F)` over `X × {0,1}^T`.
-/
theorem proposition_6_2 :
    ∃ c : ℝ, 0 < c ∧
    ∀ (F : Set Gen) (T : ℕ) (X : Set (List Bool)) (D : PMF X) (hstar : X → Bool),
      hstar ∈ e2eClass F T X →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∀ m : ℕ,
      (((F.Finite ∧ c * (Real.log F.ncard + Real.log (1 / δ)) / ε ≤ m) ∨
          (∃ v : ℕ, UnderstandingML.vcDim (e2eClass F T X) = v ∧
            c * ((v : ℝ) * Real.log (2 / ε) + Real.log (1 / δ)) / ε ≤ m)) →
        (iidSample D m).toOuterMeasure
          {xs | ∃ f ∈ F, (∀ i, e2e f T (xs i) = hstar (xs i)) ∧
            ε < endToEndError D hstar (fun x => e2e f T x)} ≤ ENNReal.ofReal δ) ∧
      (((F.Finite ∧ c * (Real.log F.ncard + Real.log (1 / δ)) / ε ≤ m) ∨
          (∃ w : ℕ, UnderstandingML.vcDim (cotLossClass F T X) = w ∧
            c * ((w : ℝ) * Real.log (2 / ε) + Real.log (1 / δ)) / ε ≤ m)) →
        ∀ fstar ∈ F, (∀ x ∈ D.support, e2e fstar T x = hstar x) →
        (iidSample D m).toOuterMeasure
          {xs | ∃ f ∈ F, (∀ i, cot f T (xs i) = cot fstar T (xs i)) ∧
            ε < endToEndError D hstar (fun x => e2e f T x)} ≤ ENNReal.ofReal δ) := by sorry

end MultiThinkCoT
