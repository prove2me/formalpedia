-- Prove2me | Theorems.Thm_MinimaxATE_Learnability_lemma_1_9
-- name    : MinimaxATE.Learnability.lemma_1_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:01:37.171197+00:00
-- url     : https://prove2.me/theorems/3bc78f5e-5385-45b9-b5c7-4f447dea7fa5
-- title:
--   Lemma 1.9 — approximate symmetry from mutual fat-shattering
-- statement:
--   There is an absolute constant $C_A\ge1$ with the following property. Let $c\in(0,1/2)$, $0<\kappa\le1/2-c$, $0<\gamma\le1/2$, $\varepsilon_P,\varepsilon_M>0$, and let $\mathcal P\subseteq[c,1-c]^{\mathcal X}$, $\mathcal M\subseteq[0,1]^{\mathcal X}$. Every $N$-point set $\{x_1,\dots,x_N\}$ mutually fat-shattered by $(\mathcal P,\mathcal M)$ at scales $(\kappa,\gamma)$ contains an $(\varepsilon_P,\varepsilon_M)$-approximately symmetric mutually fat-shattered set at scales $(\kappa,\gamma)$ (propensity gaps $d_i\ge\kappa$, outcome gaps $e_i\ge\gamma$) of size at least
--   $$\Big\lceil\frac{N}{C_A\log^2\big(\frac{1-c}{\varepsilon_P\varepsilon_M}\big)}\Big\rceil .$$
--
--   This Ramsey-type statement is the key new step of the lower bound: it lets the approximately symmetric lower bound (Theorem 5.6) apply to any mutually shattered set.
--
--   **Formalization Note.** The $N$ points are an injective sequence `Fin N → X`; the subset is a `Finset` of indices, and the restricted sequence is approximately symmetrically shattered in the sense of Definition 7. The logarithm is natural. As printed, the statement is false when $\varepsilon_P\varepsilon_M$ is close to $1-c$ (see the mission's findings); it is stated as printed.
--
--   Differences from the source:
--   - encoding: N/(C_A log²((1−c)/(ε_P ε_M))) when the logarithm is 0 (ε_P ε_M = 1 − c), where the printed bound is undefined → real division, so the bound reads ⌈0⌉ = 0; reason: Lean's x/0 = 0 on the one undefined input.
--   - reading: classes P, M → P ⊆ [c, 1−c]^X, M ⊆ [0, 1]^X; reason: the standing setting of §3 (p. 18), which also fixes the c in the bound.
--   - encoding: an N-point set; a subset that is approximately symmetrically shattered → an injective x : Fin N → X; a finset I of indices with the restricted family x|_I; reason: same sets.
-- source:
--   Cai, Kalavasis, Mamali, Mehrotra, Zampetakis, Minimax Rates for Estimation of Average Treatment Effects in Observational Studies, STOC 2027 submission (manuscript sha256 89998c39…), p. 15 (PDF 17), Lemma 1.9; restated p. 41 (PDF 43), proof p. 41-42 (PDF 43-44)

import Mathlib
import Definitions.Def_MinimaxATE_Learnability_FatDims

namespace MinimaxATE.Learnability

universe u

theorem lemma_1_9 : ∃ CA : ℝ, 1 ≤ CA ∧
    ∀ (c : ℝ), 0 < c → c < 1 / 2 →
    ∀ (κ γ : ℝ), 0 < κ → κ ≤ 1 / 2 - c → 0 < γ → γ ≤ 1 / 2 →
    ∀ (εP εM : ℝ), 0 < εP → 0 < εM →
    ∀ (X : Type u) (P M : Set (X → ℝ)),
      (∀ p ∈ P, ∀ x, p x ∈ Set.Icc c (1 - c)) → (∀ m ∈ M, ∀ x, m x ∈ Set.Icc (0 : ℝ) 1) →
    ∀ (N : ℕ) (x : Fin N → X), Function.Injective x → MutShatters P M κ γ x →
      ∃ I : Finset (Fin N),
        ApproxSymShatters P M κ γ εP εM (fun i : I => x i) ∧
        (⌈(N : ℝ) / (CA * Real.log ((1 - c) / (εP * εM)) ^ 2)⌉ : ℝ) ≤ I.card := by sorry

end MinimaxATE.Learnability
