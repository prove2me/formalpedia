-- Prove2me | Theorems.Thm_MinimaxATE_Learnability_theorem_4_2
-- name    : MinimaxATE.Learnability.theorem_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:01:37.133302+00:00
-- url     : https://prove2.me/theorems/0a5bc8b1-b76a-4b5f-bd09-ff885dde1fec
-- title:
--   Theorem 4.2 (Mendelson–Vershynin) — an empirical-$L_2$ cover inside $H$ with $\log|V_H(s)|\le C\log(8/s)\,\mathrm{fat}_{\kappa s}(H[S])$
-- statement:
--   There are universal constants $\kappa,C>0$ with the following property. Let $H\subseteq[0,1]^{\mathcal X}$ be any class of functions, $S=(S_1,\dots,S_m)$ a nonempty finite covariate sample ($m\ge1$) and $s\in(0,1)$. Then there is a finite cover $V_H(s)\subseteq H$ with
--   $$\log|V_H(s)|\le C\log(8/s)\,\mathrm{fat}_{\kappa s}(H[S])$$
--   such that for every $h\in H$ there is $h^\star\in V_H(s)$ with
--   $$\frac1{m}\sum_{i=1}^m\big(h(S_i)-h^\star(S_i)\big)^2\le s^2/4 .$$
--
--   This is the dimension-free covering bound of Mendelson and Vershynin (2003, Theorem 1) for the empirical $L_2$ distance, used to replace each class by a finite cover on every part of the partition.
--
--   **Formalization Note.** The logarithm is natural; the bound is compared in `ℝ≥0∞` with the `ℕ∞`-valued $\mathrm{fat}_{\kappa s}(H[S])$ (finite here, since the sample is finite). If $H$ is empty the cover is empty and $\log 0=0$ in Lean.
--
--   Differences from the source:
--   - generalization: S a non-empty finite covariate sample, averaged over x ∈ S → an indexed sample S : Fin m → X, m ≥ 1, repetitions allowed, averaged over indices; reason: a set S is the injective case; the paper applies the theorem to the covariates X_R, which may repeat.
-- source:
--   Cai, Kalavasis, Mamali, Mehrotra, Zampetakis, Minimax Rates for Estimation of Average Treatment Effects in Observational Studies, STOC 2027 submission (manuscript sha256 89998c39…), p. 21 (PDF 23), Theorem 4.2 (citing Mendelson and Vershynin 2003, Theorem 1)

import Mathlib
import Definitions.Def_MinimaxATE_Learnability_FatDims

open BartlettNN.Margin

namespace MinimaxATE.Learnability

universe u

theorem theorem_4_2 : ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧
    ∀ (X : Type u) (H : Set (X → ℝ)), (∀ h ∈ H, ∀ x, h x ∈ Set.Icc (0 : ℝ) 1) →
    ∀ (m : ℕ), 0 < m → ∀ (S : Fin m → X) (s : ℝ), 0 < s → s < 1 →
      ∃ V : Finset (X → ℝ), (↑V : Set (X → ℝ)) ⊆ H ∧
        ENNReal.ofReal (Real.log (V.card : ℝ)) ≤
          ENNReal.ofReal (C * Real.log (8 / s)) * (fat (proj H S) (κ * s) : ENNReal) ∧
        ∀ h ∈ H, ∃ h' ∈ V, (1 / (m : ℝ)) * ∑ i, (h (S i) - h' (S i)) ^ 2 ≤ s ^ 2 / 4 := by sorry

end MinimaxATE.Learnability
