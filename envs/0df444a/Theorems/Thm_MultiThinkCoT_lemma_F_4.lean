-- Prove2me | Theorems.Thm_MultiThinkCoT_lemma_F_4
-- name    : MultiThinkCoT.lemma_F_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:44:14.046741+00:00
-- url     : https://prove2.me/theorems/3b82c1d7-21ab-4554-8801-1cc7e30c1bdf
-- title:
--   Lemma F.4 — uniform convergence over $H_{\mathrm{boost}}(K)$ (corrected: $K\ge1$)
-- statement:
--   There is a universal constant $c>0$ such that the following holds. Let $\mathcal F$ be a base class, $T$ a generation length, $\mathcal X$ a domain with $\mathrm{VCdim}(\mathcal F^{\mathrm{e2e}\text{-}T})=v<\infty$, $h^\star\in\mathcal F^{\mathrm{e2e}\text{-}T}$, $\mathcal D$ a distribution over $\mathcal X$, $K\ge1$ and $\varepsilon,\delta\in(0,1)$. For every
--
--   $$
--   m\ \ge\ c\,\frac{K\,v\,\max\{1,\log(Kv)\}\log(2/\varepsilon)+\log\delta^{-1}}{\varepsilon},
--   $$
--
--   with probability at least $1-\delta/2$ over $S_{\mathrm{e2e}}=\{(x^{(i)},h^\star(x^{(i)}))\}_{i\le m}$, $x^{(i)}\sim_{\mathrm{iid}}\mathcal D$, every $\hat h\in H_{\mathrm{boost}}(K)$ consistent with $S_{\mathrm{e2e}}$ satisfies $L_{\mathcal D,h^\star}(\hat h)\le\varepsilon$.
--
--   This converts the zero training error of Algorithm 1's output into small population error.
--
--   **Formalization Note** The condition $K\ge1$ corrects the printed statement. For $K=0$, $H_{\mathrm{boost}}(0)$ is the constant $1$. Take $\mathcal F=\{f\}$ with $f^{\mathrm{e2e}\text{-}T}\equiv0=h^\star$, so $v=0$, and $\delta$ close to $1$; the printed condition then allows $m=0$, and the constant $1$ is consistent with the empty sample but has error $1$. Natural logarithms.
--
--   Differences from the source:
--   - correction: any K (K = 0 allowed) → 1 ≤ K; reason: counterexample: K = 0, F = {f} with f^{e2e-T} ≡ 0 = h⋆, v = 0, δ near 1 allows m = 0, and the constant 1 ∈ H_boost(0) is consistent with the empty sample but has error 1 > ε with probability 1 > δ/2
--   - encoding: log(K·VCdim(F^{e2e-T})) → max{1, log(Kv)}; reason: the paper's convention for logarithmic factors (p.16); a plain log vanishes at Kv = 1
--   - reading: any E2E consistent predictor ĥ ∈ H_boost(K) → uniform over all such predictors: the outer probability that some consistent member has error > ε is at most the stated failure probability; reason: the rule may return any consistent member; the guarantee must hold for whichever is returned
--   - encoding: a distribution D ∈ ∆(X) on X ⊆ {0,1}* → D : PMF X; reason: X is countable, so every distribution on it is a probability mass function
--   - encoding: VCdim(F^{e2e-T}) (finiteness implicit) → vcDim (e2eClass F T X) = v with v : ℕ; reason: for infinite VC dimension the threshold is infinite and the lemma is vacuous
--   - encoding: ε (and δ) unquantified in the lemma → ε, δ ∈ (0, 1); reason: the paper's accuracy and confidence parameters range over (0, 1) (Definition 6.2, Theorem 7); for ε ≥ 1 or δ ≥ 1 the conclusion holds trivially, since every error is at most 1
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), Appendix F, Lemma F.4, p.56 (PDF p.56)

import Mathlib
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_MultiThinkCoT_e2eClass
import Definitions.Def_MultiThinkCoT_hboost
import Definitions.Def_MultiThinkCoT_endToEndError

namespace MultiThinkCoT

/-- **Lemma F.4**, p.56 (PDF p.56) (corrected: `K ≥ 1`).
N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…).

There is a universal `c > 0` such that, for any base class `F`, generation length `T`, domain
`X` with `VCdim(F^{e2e-T}) = v < ∞`, any target `h⋆ ∈ F^{e2e-T}`, any distribution `D` over `X`,
any `K ≥ 1`, `ε, δ ∈ (0,1)` and any
`m ≥ c (K v max{1, log(Kv)} log(2/ε) + log δ⁻¹)/ε`, with probability at least `1 − δ/2` over
`S_e2e` (`x(i) ∼iid D`, `y(i) = h⋆(x(i))`), every `ĥ ∈ H_boost(K)` consistent with `S_e2e` has
`L_{D,h⋆}(ĥ) ≤ ε`.

**Formalization Note.**
* Correction `K ≥ 1`: for `K = 0`, `H_boost(0)` is the constant `1`; with `F = {f}`,
  `f^{e2e-T} ≡ 0 = h⋆`, `v = 0` and `δ` close to `1` the printed condition allows `m = 0`, and the
  constant `1` is consistent with the empty sample but has error `1 > ε`.
* `max{1, log(Kv)}` per the paper's convention for logarithmic factors (p.16); natural log.
* `D` is a `PMF` on the countable domain; "any consistent `ĥ`" is read uniformly over `H_boost(K)`.
-/
theorem lemma_F_4 :
    ∃ c : ℝ, 0 < c ∧
    ∀ (F : Set Gen) (T : ℕ) (X : Set (List Bool)) (v : ℕ),
      UnderstandingML.vcDim (e2eClass F T X) = v →
      ∀ (D : PMF X) (hstar : X → Bool), hstar ∈ e2eClass F T X →
      ∀ K : ℕ, 1 ≤ K → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∀ m : ℕ, c * ((K : ℝ) * v * max 1 (Real.log (K * v)) * Real.log (2 / ε)
          + Real.log (1 / δ)) / ε ≤ m →
      (iidSample D m).toOuterMeasure
        {xs | ∃ h ∈ hboost F T X K, (∀ i, h (xs i) = hstar (xs i)) ∧
          ε < endToEndError D hstar h} ≤ ENNReal.ofReal (δ / 2) := by sorry

end MultiThinkCoT
