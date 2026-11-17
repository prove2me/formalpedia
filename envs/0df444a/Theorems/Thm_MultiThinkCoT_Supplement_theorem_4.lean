-- Prove2me | Theorems.Thm_MultiThinkCoT_Supplement_theorem_4
-- name    : MultiThinkCoT.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:58:52.382738+00:00
-- url     : https://prove2.me/theorems/1b138c31-7895-41a2-b1fe-2f412a7ffe21
-- title:
--   Theorem 4 — pass@$\kappa$ bound for $\kappa$-ConsistentCoT, and $\mathrm{VCdim}(\mathcal L^{\mathrm{CoT}\text{-}T}(\mathcal F;\kappa))=O(\kappa\,\mathrm{VCdim}(\mathcal F)\log(2\kappa T))$
-- statement:
--   There is a universal constant $c>0$ such that the following holds. Let $\mathcal F$ be a base class, $\mathcal X\subseteq\{0,1\}^*$ a domain and $T$ a generation length, and consider instance-dependent CoT supervision with **unknown provenance** (Definition 6.1) from $\kappa$ generators $f_1,\dots,f_\kappa\in\mathcal F$ with $f_1^{\mathrm{e2e}\text{-}T}\equiv\dots\equiv f_\kappa^{\mathrm{e2e}\text{-}T}\equiv h_\star$ on $\mathcal X$, an input distribution $\mathcal D$ and an arbitrary source kernel $\mathcal P(\cdot\mid x)$. For all $\varepsilon,\delta\in(0,1)$, if
--
--   $$
--   m\ \ge\ c\,\frac{\mathrm{VCdim}\big(\mathcal L^{\mathrm{CoT}\text{-}T}(\mathcal F;\kappa)\big)\log(2/\varepsilon)+\log(1/\delta)}{\varepsilon},
--   $$
--
--   then with probability at least $1-\delta$ over the training set the following holds simultaneously for **every** output of the rule $\kappa$-ConsistentCoT, i.e. every $\hat f_1,\dots,\hat f_\kappa\in\mathcal F$ with $z^{(i)}\in\widehat{\mathcal Z}(x^{(i)})=\{\hat f_j^{\mathrm{CoT}\text{-}T}(x^{(i)}):j\in[\kappa]\}$ for all $i$:
--
--   1. the pass@$\kappa$ error satisfies $\Pr_{x\sim\mathcal D,\,j\sim\mathcal P(\cdot\mid x)}\big[f_j^{\mathrm{CoT}\text{-}T}(x)\notin\widehat{\mathcal Z}(x)\big]\le\varepsilon$;
--   2. if moreover $\hat f_1^{\mathrm{e2e}\text{-}T}\equiv\dots\equiv\hat f_\kappa^{\mathrm{e2e}\text{-}T}\equiv\hat h$ on $\mathcal X$ (E2E agreement), then $\mathcal L_{\mathcal D,h_\star}(\hat h)\le\varepsilon$.
--
--   In addition, for every $\mathcal F$, $\mathcal X$, $T$ and $\kappa$, with $\mathrm{VCdim}(\mathcal F)$ taken over the prefix domain $\mathcal X\times\{0,1\}^{\le T-1}$,
--
--   $$
--   \mathrm{VCdim}\big(\mathcal L^{\mathrm{CoT}\text{-}T}(\mathcal F;\kappa)\big)\ \le\ c\,\kappa\,\mathrm{VCdim}(\mathcal F)\log(2\kappa T).
--   $$
--
--   The theorem extends the single-generator CoT sample-complexity bound to $\kappa$ heterogeneous generators: the dependence on $T$ stays logarithmic, and under E2E agreement it improves on learning from end-to-end labels alone when $\kappa\ll T$.
--
--   **Formalization Note** The sample threshold and the VC bound are stated with the VC dimensions as natural numbers; when they are infinite the corresponding clause is vacuous, as in the paper. Logarithms are natural; at $\kappa T=0$ Lean's $\log 0=0$, and the loss class is then a single function, so the bound holds there as well.
--
--   Differences from the source:
--   - encoding: $x^{(i)}\sim\mathcal D$ i.i.d., then $j^{(i)}\sim\mathcal P(\cdot\mid x^{(i)})$ independently → the pairs $(x^{(i)},j^{(i)})$ i.i.d. from the joint law, with $\mathcal D$ a PMF on the countable domain; reason: the two-stage sampling of Definition 6.1 is exactly this joint law.
--   - reading: "with probability at least $1-\delta$ the rule $\kappa$-ConsistentCoT satisfies …" → the bound holds simultaneously for every tuple the rule may return (and every common $\hat h$); reason: the rule is specified only by its consistency constraint, so its guarantee must cover each consistent output.
--   - encoding: $\mathrm{VCdim}$ possibly infinite → the threshold and the VC bound are stated with finite values $w,p\in\mathbb N$, vacuous otherwise; reason: an infinite VC dimension makes the paper's threshold and bound vacuous too.
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), §7.1, Theorem 4, p.21 (PDF p.21); proof in Appendix B, pp.36–38

import Mathlib
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_MultiThinkCoT_prefixClass
import Definitions.Def_MultiThinkCoT_endToEndError
import Definitions.Def_MultiThinkCoT_Supplement_lossClassK
import Definitions.Def_MultiThinkCoT_Supplement_passErr

namespace MultiThinkCoT.Supplement

/-- **Theorem 4 (A generalization bound)**, §7.1, p.21 (PDF p.21).
N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…).

There is a universal constant `c > 0` such that for any base class `F`, domain `X`, generation
length `T`, under instance-dependent CoT supervision with unknown provenance (Definition 6.1) from
`κ` generators `f_1, …, f_κ ∈ F` with `f_1^{e2e-T} ≡ ⋯ ≡ f_κ^{e2e-T} ≡ h⋆`, for every
`ε, δ ∈ (0, 1)`, if `m ≥ c (VCdim(L^{CoT-T}(F; κ)) log(2/ε) + log(1/δ))/ε`, then with probability at
least `1 − δ` over the training set the rule κ-ConsistentCoT satisfies
`Pr_{x∼D, j∼P(·|x)}[f_j^{CoT-T}(x) ∉ Ẑ(x)] ≤ ε` and, when the E2E agreement constraint is also
imposed, `L_{D,h⋆}(ĥ) ≤ ε`. Moreover
`VCdim(L^{CoT-T}(F; κ)) ≤ c κ VCdim(F) log(2κT)`, with `VCdim(F)` over `X × {0,1}^{≤T−1}`.

**Formalization Note.**
* The rule may return any consistent tuple; the statement is uniform over all of them. The bad
  event is: some `g ∈ F^κ` that is κ-CoT-consistent with the sample (every observed trace lies in
  `candSet T g x(i)`) has pass@κ error `> ε`, or additionally satisfies E2E agreement with a common
  `ĥ` on `X` and has `L_{D,h⋆}(ĥ) > ε`. Its probability is at most `δ`, so both conclusions hold
  simultaneously with probability `≥ 1 − δ`.
* Unknown provenance: the event depends on the sample only through `(x(i), z(i))`, with
  `z(i) = f_{j(i)}^{CoT-T}(x(i))`; the pairs `(x(i), j(i))` are i.i.d. from `jointLaw D P` for an
  arbitrary kernel `P : X → PMF (Fin κ)` fixed before sampling.
* Realizability `f_j^{e2e-T} ≡ h⋆` is required at every point of `X` (the convention of the
  published mission).
* The sample threshold uses `w = VCdim(L^{CoT-T}(F; κ)) : ℕ`; when this VC dimension is infinite
  the threshold is never met and the first clause is vacuous, as in the paper. In the VC bound
  `VCdim(F) = p : ℕ` (vacuous when infinite). `log` is the natural logarithm; at `κ = 0` or
  `T = 0`, `log(2κT) = log 0 = 0` in Lean, and the loss class is then a single function.
* VC dimensions are `UnderstandingML.vcDim`, of `L^{CoT-T}(F; κ)` over `X × {0,1}^T` and of
  `F` over the prefix domain (`MultiThinkCoT.prefixClass`).
-/
theorem theorem_4 :
    ∃ c : ℝ, 0 < c ∧
      (∀ (F : Set Gen) (X : Set (List Bool)) (T κ : ℕ) (f : Fin κ → Gen), (∀ j, f j ∈ F) →
        ∀ hstar : X → Bool, (∀ (j : Fin κ) (x : X), e2e (f j) T x = hstar x) →
        ∀ (D : PMF X) (P : X → PMF (Fin κ)) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        ∀ w m : ℕ, UnderstandingML.vcDim (lossClassK F T X κ) = w →
          c * ((w : ℝ) * Real.log (2 / ε) + Real.log (1 / δ)) / ε ≤ m →
          (iidSample (jointLaw D P) m).toOuterMeasure
            {s | ∃ g : Fin κ → Gen, (∀ j, g j ∈ F) ∧
              (∀ i, cot (f (s i).2) T (s i).1.1 ∈ candSet T g (s i).1.1) ∧
              (ε < passErr D P T f (candSet T g) ∨
                ∃ h : X → Bool, (∀ (j : Fin κ) (x : X), e2e (g j) T x = h x) ∧
                  ε < endToEndError D hstar h)} ≤ ENNReal.ofReal δ) ∧
      (∀ (F : Set Gen) (T : ℕ) (X : Set (List Bool)) (κ p : ℕ),
        UnderstandingML.vcDim (prefixClass F T X) = p →
        ∃ w : ℕ, UnderstandingML.vcDim (lossClassK F T X κ) = w ∧
          (w : ℝ) ≤ c * κ * p * Real.log (2 * κ * T)) := by sorry

end MultiThinkCoT.Supplement
