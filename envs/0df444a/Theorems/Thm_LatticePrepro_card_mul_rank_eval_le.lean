-- Prove2me | Theorems.Thm_LatticePrepro_card_mul_rank_eval_le
-- name    : LatticePrepro.card_mul_rank_eval_le
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:24:54.247456+00:00
-- url     : https://prove2.me/theorems/b5d8f901-7279-4c5a-b950-fb4a996cb922
-- title:
--   Lemma A.6, inequality (32) — rank of a polynomial matrix at $\gamma$ versus its evaluations
-- statement:
--   Let $\mathbb{S}$ be a finite field with $q$ elements, $K$ a field that is an $\mathbb{S}$-algebra (an extension of $\mathbb{S}$), and $\gamma\in K$. Let $\ell,\Delta$ be natural numbers and $H(X)$ an $\ell\times\ell$ matrix over $\mathbb{S}[X]$ all of whose entries have degree at most $\Delta$. Write $H(\gamma)\in K^{\ell\times\ell}$ and $H(s)\in\mathbb{S}^{\ell\times\ell}$ ($s\in\mathbb{S}$) for the entrywise evaluations. Then
--   $$q\cdot\operatorname{rank}_K H(\gamma)\;\le\;\sum_{s\in\mathbb{S}}\operatorname{rank}_{\mathbb{S}}H(s)\;+\;\Delta\cdot\operatorname{rank}_K H(\gamma).$$
--   Equivalently, when $\Delta\le q$: $(q-\Delta)\cdot\operatorname{rank}_K H(\gamma)\le\sum_{s\in\mathbb{S}}\operatorname{rank}_{\mathbb{S}}H(s)$.
--
--   This is the Fancsali–Sziklai-type estimate (32) in the proof of Lemma A.6. Applied to the polynomial matrix of an evaluation table (Definition A.5), whose value at $\gamma$ is the Hankel matrix of the moments and whose value at $s$ has rank at most the weight of column $s$, it gives the weight bound $(q-\Delta)\cdot\operatorname{rank}\le\mathrm{wt}(y)$ used for soundness in Theorem A.8.
--
--   **Formalization Note**: The inequality is stated without natural-number subtraction. The paper bounds the rank $\rho$ of $H(X)$ over $\mathbb{S}(X)$ and separately notes $\operatorname{rank}H(\gamma)\le\rho$; the Lean statement bounds $\operatorname{rank}_K H(\gamma)$ directly, which is what the soundness argument needs. Ranks are Mathlib's `Matrix.rank`, and the matrix is indexed by `Fin ℓ`. The statement is generic and involves no evaluation tables.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Lemma A.6 (\label{lem:table-rank}), inequality (32) (\label{eq:polynomial-average-rank}) in its proof; Lean: LatticePrepro/Tables/PolyMatrixRank.lean, LatticePrepro.card_mul_rank_eval_le

import Mathlib

open Polynomial Matrix

theorem LatticePrepro.card_mul_rank_eval_le {𝕊 : Type*} [Field 𝕊] [Fintype 𝕊] [DecidableEq 𝕊]
    {K : Type*} [Field K] [Algebra 𝕊 K] (γ : K) {ℓ Δ : ℕ}
    (H : Matrix (Fin ℓ) (Fin ℓ) 𝕊[X]) (hdeg : ∀ i j, (H i j).natDegree ≤ Δ) :
    Fintype.card 𝕊 * (H.map (aeval γ)).rank ≤
      (∑ s : 𝕊, (H.map (eval s)).rank) + Δ * (H.map (aeval γ)).rank := by sorry
