-- Prove2me | Theorems.Thm_MultiCorrectPAC_Demo_lemma_11
-- name    : MultiCorrectPAC.Demo.lemma_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:45:42.800579+00:00
-- url     : https://prove2.me/theorems/c45bb8e3-2486-4adc-be72-4b27a2bb0375
-- title:
--   Lemma 11 — most probable labels and plurality votes err at most ℓ + 1 times as often as the randomized prediction or the average voter
-- statement:
--   Let $A$ be a set of at most $\ell$ labels. If a most probable label of a distribution $p$ on $\mathcal Y$ lies outside $A$, then
--   $$p(\mathcal Y\setminus A)\ge\frac1{\ell+1}.$$
--   Consequently the error of a most probable label is at most $\ell+1$ times the error of the randomized prediction: if $g(x)$ is a most probable label of $p(\cdot\mid x)$ for every $x$, then $L_{P,h}(g)\le(\ell+1)L_{P,h}(p)$. Likewise a plurality vote $g$ of $T\ge1$ voters $g_1,\dots,g_T$ is invalid at an input only if at least a $1/(\ell+1)$ fraction of the votes there is invalid, so
--   $$L_{P,h}(g)\le(\ell+1)\cdot\frac1T\sum_{j=1}^TL_{P,h}(g_j).$$
--
--   This replaces the factor two of binary majority votes and is how randomized predictions and ensembles become single predictors with comparable error (Lemma 40).
--
--   Differences from the source:
--   - encoding: standing assumptions (§5.1): X and Y nonempty countable with discrete σ-algebras, ℓ ≥ 1 → [Countable X] [Nonempty X] [Countable Y] [Nonempty Y] (Fintype Y where Y is finite) and hℓ : 1 ≤ ℓ; reason: the standing assumptions of §5.1 made explicit
--   - encoding: distributions on the countable spaces X, X × Y; probability over m i.i.d. examples and the seed ω ∼ Unif([0,1]); errors (3) → PMFs; the probability of an event is ∑' σ, (∏ᵢ D(σᵢ)) · volume {ω ∈ unitInterval | event}; errors are values in ℝ≥0∞ and ε enters as ENNReal.ofReal ε; 'with probability ≥ 1 − δ' is stated as failure probability ≤ δ; reason: the product law on a countable sample space, written out; same numbers
--   - encoding: error of a most probable label / of a plurality vote under P and h (setting of (3): P(supp(h)) = 1, h(x) ∈ A ∪ {⋆}) → h with every defined value InA ℓ, SupportedIn P h; g with IsMostProbable (p x) (g x) resp. IsPlurality (fun j => votes j x) (g x) at every x; "fraction of votes" as ncard of the invalid voters ≥ T/(ℓ+1); reason: the setting of the errors (3) made explicit
--   - encoding: a set A of at most ℓ labels; mass of Y \ A → A : Finset Y with card ≤ ℓ; p.toOuterMeasure (↑A)ᶜ ≥ ENNReal.ofReal (1/(ℓ+1)); reason: Lean convention
--   - generalization: when Y is finite, k = |Y| and ℓ ≤ k (§5.1, p. 25) → [Countable Y] [Nonempty Y] only; a finite Y with |Y| < ℓ is not excluded; reason: ℓ enters only as a bound on the sizes of correct-label sets, which is how the paper's own argument uses it (Remark 54, p. 76, views a class with a larger ℓ); on every Y the paper allows the statement is the paper's
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), p. 32 (PDF 34), Lemma 11

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses
import Definitions.Def_MultiCorrectPAC_Demo_Learning

open scoped ENNReal

namespace MultiCorrectPAC.Demo

theorem lemma_11 (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {X Y : Type*} [Countable X] [Nonempty X] [Countable Y]
    [Nonempty Y] :
    (∀ (A : Finset Y) (p : PMF Y) (y₀ : Y), A.card ≤ ℓ → IsMostProbable p y₀ → y₀ ∉ A →
      ENNReal.ofReal (1 / ((ℓ : ℝ) + 1)) ≤ p.toOuterMeasure (↑A : Set Y)ᶜ) ∧
    (∀ (P : PMF X) (h : Hyp X Y) (p : X → PMF Y) (g : X → Y),
      (∀ x A, h x = some A → InA ℓ A) → SupportedIn P h →
      (∀ x, IsMostProbable (p x) (g x)) →
        predLoss P h g ≤ ((ℓ : ℝ≥0∞) + 1) * randLoss P h p) ∧
    (∀ (P : PMF X) (h : Hyp X Y) (T : ℕ) (votes : Fin T → X → Y) (g : X → Y), 0 < T →
      (∀ x A, h x = some A → InA ℓ A) → SupportedIn P h →
      (∀ x, IsPlurality (fun j => votes j x) (g x)) →
        (∀ x, IsInvalid h x (g x) →
          (T : ℝ) / ((ℓ : ℝ) + 1) ≤ ({j | IsInvalid h x (votes j x)}.ncard : ℝ)) ∧
        predLoss P h g ≤ ((ℓ : ℝ≥0∞) + 1) / (T : ℝ≥0∞) * ∑ j, predLoss P h (votes j)) := by sorry

end MultiCorrectPAC.Demo
