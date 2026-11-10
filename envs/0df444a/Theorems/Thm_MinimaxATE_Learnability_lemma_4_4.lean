-- Prove2me | Theorems.Thm_MinimaxATE_Learnability_lemma_4_4
-- name    : MinimaxATE.Learnability.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:02:34.468978+00:00
-- url     : https://prove2.me/theorems/ab07e768-e13b-4ad6-be08-7219a4942d90
-- title:
--   Lemma 4.4 — error of the per-part AIPW estimator
-- statement:
--   For every $c\in(0,1/2)$ there is a constant $C_c>0$, depending only on $c$, such that the following holds. Let $\mathcal P\subseteq[c,1-c]^{\mathcal X}$, $\mathcal M\subseteq[0,1]^{\mathcal X}$, $D\in\mathcal D(\mathcal P,\mathcal M,c)$ with true nuisances $p^\star,m^\star_0,m^\star_1$ (versions realizing $D$), and $n\ge1$. Draw $(X_i,T_i,Y_i)_{i\le n}$ i.i.d. from $C_D$ and split the indices independently into $D_T$ and $D_V$ with probability $1/2$. Let $\Pi=\Pi(X)$ be a $\sigma(X)$-measurable partition of $[n]$, and, for every part $R$, let $\hat p_R\in[c,1-c]^{\mathcal X}$ and $\hat m_{R,0},\hat m_{R,1}\in[0,1]^{\mathcal X}$ be fixed given the training information $\mathcal F_{\mathrm{tr}}=\sigma(X,D_T,D_V,\{(T_i,Y_i):i\in D_T\})$ (and measurable). Let $\hat\tau$ be the per-part clipped AIPW estimator evaluated on $D_V$. Then for every $\delta\in(0,1)$, with probability at least $1-\delta$,
--   $$|\hat\tau-\tau_D|\le C_c\Big(\sqrt{\frac{\log(1/\delta)}n}+\sum_{R\in\Pi}\frac{|R|}n\sqrt{L_{P,R}(\hat p_R)}\Big(\sqrt{L_{M,R,0}(\hat m_{R,0})}+\sqrt{L_{M,R,1}(\hat m_{R,1})}\Big)\Big),$$
--   where $L_{P,R}(\hat p_R)=\frac1{|R|}\sum_{i\in R}(\hat p_R(X_i)-p^\star(X_i))^2$ and $L_{M,R,t}(\hat m_{R,t})=\frac1{|R|}\sum_{i\in R}(\hat m_{R,t}(X_i)-m^\star_t(X_i))^2$.
--
--   It transfers the per-part nuisance errors into the error of the ATE estimate, and is the last ingredient of the upper bound (Theorem 1.8).
--
--   **Formalization Note.** The probability space is (sample, split) with law `splitSampleLaw D n`. The nuisances are functions of (sample, split, part) that depend on the sample only through the covariates and the training observations (this is "fixed given $\mathcal F_{\mathrm{tr}}$") and are jointly measurable. The failure set is measured directly (outer measure if it were not measurable). As printed, the statement is false for $\delta$ near $1$ (see the mission's findings); it is stated as printed.
--
--   Differences from the source:
--   - reading: ≲_c → an explicit constant C_c > 0 chosen after c and before the classes, the study, n, the partition, the nuisances and δ; reason: "≲_c" is the paper's notation for a c-dependent constant.
--   - reading: "Given p̂_R, m̂_{R,0}, m̂_{R,1} for all R ∈ Π" → nuisances depending on the sample only through F_tr, with values in [c, 1−c] and [0, 1], jointly measurable; reason: the proof's conditioning on F_tr (p. 49) and the standing measurability assumption of p. 19.
--   - reading: "with probability 1 − δ" → for every δ ∈ (0, 1), failure probability ≤ δ; reason: the paper's convention for high-probability bounds.
--   - encoding: n ∈ ℕ → 0 < n; reason: the printed bound divides by n.
--   - reading: Π, the partition of Algorithm 1 → any partition map from covariate vectors to partitions of [n] with measurable level sets; reason: App. A.1 (p. 49) states the lemma for nuisances fitted on each part of a covariate-dependent partition; Lemma 4.1's partition is an instance.
--   - reading: τ = τ_D and the true nuisances p⋆, m⋆_t in L_{P,R}, L_{M,R,t}; classes P, M → D ∈ D(P, M, c) with P ⊆ [c, 1−c]^X, M ⊆ [0, 1]^X, and any a.s. versions p⋆, m⋆_0, m⋆_1 of its nuisances; reason: the standing setting of §3 (p. 18); the nuisances are only defined almost everywhere.
-- source:
--   Cai, Kalavasis, Mamali, Mehrotra, Zampetakis, Minimax Rates for Estimation of Average Treatment Effects in Observational Studies, STOC 2027 submission (manuscript sha256 89998c39…), p. 22 (PDF 24), Lemma 4.4; proof p. 49-50 (PDF 51-52)

import Mathlib
import Definitions.Def_MinimaxATE_Learnability_DRScore

open MeasureTheory

namespace MinimaxATE.Learnability

universe u

theorem lemma_4_4 : ∀ (c : ℝ), 0 < c → c < 1 / 2 → ∃ C : ℝ, 0 < C ∧
    ∀ (X : Type u) [MeasurableSpace X] (P M : Set (X → ℝ)),
      (∀ p ∈ P, ∀ x, p x ∈ Set.Icc c (1 - c)) → (∀ m ∈ M, ∀ x, m x ∈ Set.Icc (0 : ℝ) 1) →
    ∀ D ∈ DClass P M c, ∀ (pS m₀S m₁S : X → ℝ), Realizes D pS m₀S m₁S →
    ∀ (n : ℕ), 0 < n →
    ∀ (part : (Fin n → X) → Finpartition (Finset.univ : Finset (Fin n))),
      (∀ π, MeasurableSet {x : Fin n → X | part x = π}) →
    ∀ (pH m₀H m₁H : (Fin n → Obs X) → (Fin n → Bool) → Finset (Fin n) → X → ℝ),
      (∀ z z' : Fin n → Obs X, ∀ b : Fin n → Bool, (∀ i, (z i).1 = (z' i).1) →
        (∀ i, b i = true → z i = z' i) →
        pH z b = pH z' b ∧ m₀H z b = m₀H z' b ∧ m₁H z b = m₁H z' b) →
      (∀ R : Finset (Fin n),
        Measurable (fun w : ((Fin n → Obs X) × (Fin n → Bool)) × X => pH w.1.1 w.1.2 R w.2) ∧
        Measurable (fun w : ((Fin n → Obs X) × (Fin n → Bool)) × X => m₀H w.1.1 w.1.2 R w.2) ∧
        Measurable (fun w : ((Fin n → Obs X) × (Fin n → Bool)) × X => m₁H w.1.1 w.1.2 R w.2)) →
      (∀ z b R x, pH z b R x ∈ Set.Icc c (1 - c) ∧ m₀H z b R x ∈ Set.Icc (0 : ℝ) 1 ∧
        m₁H z b R x ∈ Set.Icc (0 : ℝ) 1) →
    ∀ (δ : ℝ), 0 < δ → δ < 1 →
      splitSampleLaw D n
        {w | C * (Real.sqrt (Real.log (1 / δ) / n) +
              ∑ R ∈ (part (fun i => (w.1 i).1)).parts, ((R.card : ℝ) / n) *
                Real.sqrt (partLoss (fun i => (w.1 i).1) R (pH w.1 w.2 R) pS) *
                (Real.sqrt (partLoss (fun i => (w.1 i).1) R (m₀H w.1 w.2 R) m₀S) +
                  Real.sqrt (partLoss (fun i => (w.1 i).1) R (m₁H w.1 w.2 R) m₁S))) <
            |aipwPartition (part (fun i => (w.1 i).1)) (pH w.1 w.2) (m₀H w.1 w.2) (m₁H w.1 w.2)
                w.1 w.2 - ate D|} ≤ ENNReal.ofReal δ := by sorry

end MinimaxATE.Learnability
