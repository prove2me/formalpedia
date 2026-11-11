-- Prove2me | Theorems.Thm_OptAbstention_TLA_lemma_6_7
-- name    : OptAbstention.TLA.lemma_6_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:08:23.233202+00:00
-- url     : https://prove2.me/theorems/247729ad-d2fc-44e7-99a9-1684f30467d3
-- title:
--   Lemma 6.7: optimal $\mathrm{LP}_{\mathrm{TLA}}$ solutions have selective error $\le\Pr_D[h\ne f]+\varepsilon$ and, on $(S_{\mathrm{cln}},\theta)$-corruptions, abstention $\le\theta$
-- statement:
--   Let $X\subseteq\mathbb R^d$, $B\ge1$, $\varepsilon,\delta\in(0,1)$, $h:X\to\{\pm1\}$, $D$ a distribution on $X$, $\mathcal C$ a class with $\ell=L_1(\varepsilon,B,\mathcal C,D)$, and for $\theta\in[0,1)$ let $\tau_\theta=\frac{\varepsilon}{3B(1-\theta)\binom{d+\ell}{\ell}}$, $R_\theta=\frac1{1-\theta}$. There are universal $C,k$ such that if $S_{\mathrm{train}},S_{\mathrm{cln}}$ are independent i.i.d. samples from $D$ of sizes at least $C\,(M_{D,\ell}B(d+1)^\ell/(\varepsilon\delta))^k$, then:
--
--   1. with probability at least $1-\delta$ over $S_{\mathrm{train}}$, for every $f\in\mathcal C$, multiset $S_{\mathrm{test}}$, $\theta\in[0,1)$ and optimal $(u,w,z)$ of $\mathrm{LP}_{\mathrm{TLA}}(S_{\mathrm{train}},S_{\mathrm{test}},h,\ell,\tau_\theta,R_\theta)$,
--   $$\Pr_{x\sim U(S_{\mathrm{test}}),\,g(x)\sim\mathrm{Be}(z_x)}[h(x)\ne f(x)\wedge g(x)=1]\le\Pr_{x\sim D}[h(x)\ne f(x)]+\varepsilon ;$$
--   2. with probability at least $1-\delta$ over $(S_{\mathrm{train}},S_{\mathrm{cln}})$, for every $\theta\in[0,1)$ and every $(S_{\mathrm{cln}},\theta)$-corruption $S_{\mathrm{test}}$, the LP is feasible and every optimal solution satisfies $\Pr[g(x)=0]\le\theta$.
--
--   **Formalization Note.** The Bernoulli probabilities are written in closed form, $\frac1{|S_{\mathrm{test}}|}\sum_x z_x\mathbf 1\{h(x)\ne f(x)\}$ and $\frac1{|S_{\mathrm{test}}|}\sum_x(1-z_x)$; at an optimum $z_x=\min(R^{-1}|S_{\mathrm{test}}|w_x,1)\in[0,1]$.
--
--   Differences from the source:
--   - reading: h: X → {±1} and C ⊆ {±1}^X → h and every f ∈ C measurable, values ±1 as reals; reason: Pr_D[h(x) ≠ f(x)] and E_D[h(x)x^α] are defined only for measurable functions
--   - encoding: |S_train|, |S_cln| ≳ poly(M_{D,ℓ}B(d+1)^ℓ/(εδ)) → m, n ≥ C·(M_{D,ℓ}·B(d+1)^ℓ/(εδ))^k in [0,∞], C and k universal and fixed first; reason: M_{D,ℓ} = ∞ makes the hypothesis unsatisfiable, as in the source
--   - encoding: Pr over x ∼ U(S_test), g(x) ∼ Be(z_x) → (1/|S_test|)∑ z_x·1{h ≠ f} and (1/|S_test|)∑(1 − z_x); reason: the probabilities computed in closed form
--   - encoding: multiset S_test; (S_cln, θ)-corruption S_test → lists of any length n′ in item 1 (n′ = 0 has no optimal solution); lists of length |S_cln| in item 2; reason: a corruption has the cardinality of S_cln
--   - encoding: probability at least 1 − δ → the measure (outer measure) of the failure set is at most δ; reason: equivalent for measurable events, and never weaker
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 16, Lemma 6.7

import Mathlib
import Definitions.Def_OptAbstention_TLA_Sandwiching
import Definitions.Def_OptAbstention_TLA_Empirical
import Definitions.Def_OptAbstention_TLA_Reweighting

open MeasureTheory

namespace OptAbstention.TLA

open Classical in
/-- Lemma 6.7, p. 16, with `τ_θ = ε/(3B(1−θ)C(d+ℓ,ℓ))`, `R_θ = 1/(1−θ)` and
`|S_train|, |S_cln| ≥ C·(M_{D,ℓ}B(d+1)^ℓ/(εδ))^k`. The Bernoulli probabilities are in closed
form: `Pr[h ≠ f ∧ g = 1] = (1/|S_test|) ∑ z_x 1{h(x) ≠ f(x)}`, `Pr[g = 0] = (1/|S_test|) ∑ (1 − z_x)`.
Item 1 is over `S_train` alone; item 2 over the independent pair `(S_train, S_cln)`. -/
theorem lemma_6_7 : ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (d : ℕ) (X : Set (Pt d)) (D : Measure X) [IsProbabilityMeasure D] (Cl : Set (X → ℝ))
      (h : X → ℝ) (B ε δ : ℝ) (ℓ : ℕ), IsConceptClass X Cl → IsConcept X h → 1 ≤ B →
      0 < ε → ε < 1 → 0 < δ → δ < 1 → IsL1Degree D ε B Cl ℓ → ∀ m n : ℕ,
      ENNReal.ofReal C *
          (momentBound D ℓ * ENNReal.ofReal (B * ((d : ℝ) + 1) ^ ℓ / (ε * δ))) ^ k
          ≤ (m : ENNReal) →
      ENNReal.ofReal C *
          (momentBound D ℓ * ENNReal.ofReal (B * ((d : ℝ) + 1) ^ ℓ / (ε * δ))) ^ k
          ≤ (n : ENNReal) →
      (Measure.pi fun _ : Fin m => D)
          {S | ¬ ∀ f ∈ Cl, ∀ (n' : ℕ) (T : Fin n' → X) (θ : ℝ), 0 ≤ θ → θ < 1 →
            ∀ (u : Fin m → ℝ) (w z : Fin n' → ℝ),
              LPOptimal S T h ℓ (ε / (3 * B * (1 - θ) * ((d + ℓ).choose ℓ : ℝ))) (1 / (1 - θ))
                u w z →
              (∑ j, z j * (if h (T j) ≠ f (T j) then 1 else 0)) / n' ≤
                (D {x | h x ≠ f x}).toReal + ε}
          ≤ ENNReal.ofReal δ ∧
      ((Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin n => D))
          {q | ¬ ∀ θ : ℝ, 0 ≤ θ → θ < 1 → ∀ T : Fin n → X, IsCorruption q.2 T θ →
            LPIsFeasible q.1 T h ℓ (ε / (3 * B * (1 - θ) * ((d + ℓ).choose ℓ : ℝ)))
                (1 / (1 - θ)) ∧
              ∀ (u : Fin m → ℝ) (w z : Fin n → ℝ),
                LPOptimal q.1 T h ℓ (ε / (3 * B * (1 - θ) * ((d + ℓ).choose ℓ : ℝ)))
                  (1 / (1 - θ)) u w z →
                (∑ j, (1 - z j)) / n ≤ θ}
          ≤ ENNReal.ofReal δ := by sorry

end OptAbstention.TLA
