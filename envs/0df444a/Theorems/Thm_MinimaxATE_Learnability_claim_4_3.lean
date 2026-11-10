-- Prove2me | Theorems.Thm_MinimaxATE_Learnability_claim_4_3
-- name    : MinimaxATE.Learnability.claim_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:02:26.754027+00:00
-- url     : https://prove2.me/theorems/747fe4f6-92de-4dd8-a3e3-444b7fb8d89c
-- title:
--   Claim 4.3 — ERM over a finite cover: $L_{P,R}(\hat p_R)\le 3s^2/4+C(\log|V_{P,R}(s)|+\log 4/\eta)/|R|$ w.p. $1-\eta$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $c\in(0,1/2)$ and $\mathcal P\subseteq[c,1-c]^{\mathcal X}$. Condition on covariates $x_1,\dots,x_n$ and let $R\subseteq[n]$ be a nonempty part. Let $p^\star\in\mathcal P$ be the true propensity: the treatments $T_i\sim\mathrm{Bernoulli}(p^\star(x_i))$ and the training indicators $\mathbf 1\{i\in D_T\}\sim\mathrm{Bernoulli}(1/2)$ are all independent. Fix $s>0$ and let $V=V_{P,R}(s)\subseteq\mathcal P$ be a finite $s$-cover of $\mathcal P$ for the empirical $L_2$ distance on $R$: every $p\in\mathcal P$ has $v\in V$ with $\frac1{|R|}\sum_{i\in R}(p(x_i)-v(x_i))^2\le s^2/4$. With
--   $$\hat L_{P,R}(p)=\frac2{|R|}\sum_{i\in R\cap D_T}(T_i-p(x_i))^2,\qquad L_{P,R}(p)=\frac1{|R|}\sum_{i\in R}(p(x_i)-p^\star(x_i))^2,$$
--   let $\hat p_R=\arg\min_{p\in V}\hat L_{P,R}(p)$. Then for every $\eta\in(0,1)$, with probability at least $1-\eta$,
--   $$L_{P,R}(\hat p_R)\le\frac{3s^2}4+C\,\frac{\log|V_{P,R}(s)|+\log(4/\eta)}{|R|}.$$
--
--   This is the generalization guarantee for the per-part nuisance fit; it is what turns the cover size of Theorem 4.2 into an error bound.
--
--   **Formalization Note.** The probability space is $\{0,1\}^n\times\{0,1\}^n$ (treatments and training indicators) with the product law above; the event bounded by $\eta$ is "some empirical minimizer over $V$ violates the bound", so ties are covered for every choice of minimizer.
--
--   Differences from the source:
--   - reading: "Fix s > 0 and R ∈ Π" with the probability over the sample → conditional on the covariates x (fixed), R any nonempty subset of indices, randomness = treatments and the random split; reason: the proof (p. 27) conditions on X, and Π is σ(X)-measurable, hence fixed.
--   - reading: p̂_R = arg min → every empirical minimizer over V satisfies the bound on the same event; reason: the argmin is not unique in general; this is the strongest reading and the one the proof gives.
--   - reading: V_{P,R}(s), an s-cover of P on R, and the true propensity p⋆ → any finite V ⊆ P with, for every p ∈ P, some v ∈ V at empirical squared distance ≤ s²/4 on R; p⋆ ∈ P with values in [c, 1−c]; reason: the cover of Theorem 4.2 (p. 21) and realizability (p. 27); the claim is used for that cover, which is an instance.
-- source:
--   Cai, Kalavasis, Mamali, Mehrotra, Zampetakis, Minimax Rates for Estimation of Average Treatment Effects in Observational Studies, STOC 2027 submission (manuscript sha256 89998c39…), p. 21 (PDF 23), Claim 4.3; proof p. 27-28 (PDF 29-30)

import Mathlib
import Definitions.Def_MinimaxATE_Learnability_DRScore

open MeasureTheory

namespace MinimaxATE.Learnability

universe u

theorem claim_4_3 : ∃ C : ℝ, 0 < C ∧
    ∀ (c : ℝ), 0 < c → c < 1 / 2 →
    ∀ (X : Type u) (P : Set (X → ℝ)), (∀ p ∈ P, ∀ x, p x ∈ Set.Icc c (1 - c)) →
    ∀ (n : ℕ) (x : Fin n → X) (R : Finset (Fin n)), R.Nonempty →
    ∀ pStar ∈ P, ∀ (s : ℝ), 0 < s →
    ∀ V : Finset (X → ℝ), (↑V : Set (X → ℝ)) ⊆ P →
      (∀ p ∈ P, ∃ v ∈ V, partLoss x R p v ≤ s ^ 2 / 4) →
    ∀ (η : ℝ), 0 < η → η < 1 →
      (Measure.pi fun i : Fin n => (bernoulliMeasure (pStar (x i))).prod fairCoin)
          {ω | ∃ p ∈ V, (∀ q ∈ V, empLossP x R ω p ≤ empLossP x R ω q) ∧
            3 * s ^ 2 / 4 + C * (Real.log (V.card : ℝ) + Real.log (4 / η)) / (R.card : ℝ) <
              partLoss x R p pStar} ≤ ENNReal.ofReal η := by sorry

end MinimaxATE.Learnability
