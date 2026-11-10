-- Prove2me | Theorems.Thm_MinimaxATE_Learnability_lemma_4_1
-- name    : MinimaxATE.Learnability.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:01:25.777608+00:00
-- url     : https://prove2.me/theorems/10b8884e-d0ef-49b1-9859-b98b3d3669b9
-- title:
--   Lemma 4.1 — a σ(X)-measurable sample partition with $\mathrm{fat}_a(P[X_R])\,\mathrm{fat}_a(M[X_R])\le 2d_a|R|$ on every part
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $c\in(0,1/2)$, let $(\mathcal X,\mathcal A)$ be a measurable space, $\mathcal P\subseteq[c,1-c]^{\mathcal X}$, $\mathcal M\subseteq[0,1]^{\mathcal X}$, fix $a>0$ and $n\in\mathbb N$, and write $d_a=\mathrm{fat}^{\mathrm{mut}}_{a,a}(\mathcal P,\mathcal M)$. Then there is a partition $\Pi(X)$ of $[n]$, depending measurably on the covariates $X=(X_1,\dots,X_n)$, such that for every $X$:
--   1. $|\Pi(X)|\le C\,(1+\log_+(n/d_a))$, where $\log_+(t)=\max\{\log t,0\}$;
--   2. for every part $R\in\Pi(X)$,
--   $$\mathrm{fat}_a(\mathcal P[X_R])\cdot\mathrm{fat}_a(\mathcal M[X_R])\le 2\,d_a\,|R|.$$
--
--   The partition lets the estimator rely, on each group of the sample, on whichever class is simple there; its size controls the number of nuisance fits.
--
--   **Formalization Note.** $\Pi$ is a function from covariate vectors `Fin n → X` to `Finpartition` of `Fin n`, measurable in the sense that each value is taken on a measurable set of covariate vectors (the codomain is finite). $\mathcal P[X_R]$ is the projected class on the index type of $R$ (repeated covariates allowed). The product and the right-hand side are computed in `ℕ∞` ($d_a=\infty$ allowed). $\log_+(n/d_a)$ is read as $0$ when $d_a=\infty$ ($n/\infty=0$) and, with real division, when $d_a=0$.
--
--   Differences from the source:
--   - reading: |Π| ≤ C(1 + log₊(n/d_a)) with d_a possibly 0 → real division n/0 = 0, so the bound is C when d_a = 0; reason: the printed n/0 is undefined; this is the stronger reading (and n/∞ = 0 is the value when d_a = ∞).
--   - reading: "there is σ(X)-measurable partition Π of [n] and an algorithm that, given as input X, a, d_a, P, M, outputs Π" → there is a map from covariate vectors to partitions whose level sets are measurable; reason: with no computational model for the infinite input, the algorithm is the map X ↦ Π(X).
--   - reading: C → one absolute constant, chosen before c, P, M, a, n; reason: the lemma is combinatorial and names no dependence.
--   - reading: concept classes P, M (the lemma names no range) → P ⊆ [c, 1−c]^X, M ⊆ [0, 1]^X for some c ∈ (0, 1/2); reason: the standing setting of §3 (p. 18); the constant C is still chosen before c.
-- source:
--   Cai, Kalavasis, Mamali, Mehrotra, Zampetakis, Minimax Rates for Estimation of Average Treatment Effects in Observational Studies, STOC 2027 submission (manuscript sha256 89998c39…), p. 20 (PDF 22), Lemma 4.1

import Mathlib
import Definitions.Def_MinimaxATE_Learnability_FatDims

open BartlettNN.Margin

namespace MinimaxATE.Learnability

universe u

theorem lemma_4_1 : ∃ C : ℝ, 0 < C ∧
    ∀ (c : ℝ), 0 < c → c < 1 / 2 →
    ∀ (X : Type u) [MeasurableSpace X] (P M : Set (X → ℝ)),
      (∀ p ∈ P, ∀ x, p x ∈ Set.Icc c (1 - c)) → (∀ m ∈ M, ∀ x, m x ∈ Set.Icc (0 : ℝ) 1) →
    ∀ (a : ℝ), 0 < a → ∀ (n : ℕ),
      ∃ part : (Fin n → X) → Finpartition (Finset.univ : Finset (Fin n)),
        (∀ π, MeasurableSet {x : Fin n → X | part x = π}) ∧
        ∀ x : Fin n → X,
          (((part x).parts.card : ℕ) : ℝ) ≤
              C * (1 + (if mutFat P M a a = ⊤ then 0 else
                max (Real.log ((n : ℝ) / ((mutFat P M a a).toNat : ℝ))) 0)) ∧
          ∀ R ∈ (part x).parts,
            fat (proj P (fun i : R => x i)) a * fat (proj M (fun i : R => x i)) a ≤
              2 * mutFat P M a a * (R.card : ℕ∞) := by sorry

end MinimaxATE.Learnability
