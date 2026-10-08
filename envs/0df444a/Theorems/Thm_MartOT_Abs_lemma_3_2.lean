-- Prove2me | Theorems.Thm_MartOT_Abs_lemma_3_2
-- name    : MartOT.Abs.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:14.777213+00:00
-- url     : https://prove2.me/theorems/a84cf562-8b29-40cb-ac34-493a85fdb39b
-- title:
--   Lemma 3.2, p. 19 — if uncountably many fibres Γ_a have ≥ k points, some k-tuple is approximated from the right and from the left
-- statement:
--   For $\Gamma\subseteq\mathbb R^2$ write $\Gamma_a=\{y\in\mathbb R:(a,y)\in\Gamma\}$. Let $k\ge1$ be an integer and assume that there are uncountably many $a\in\mathbb R$ with $|\Gamma_a|\ge k$.
--
--   Then there exist $a$ and $b_1<\dots<b_k$ in $\Gamma_a$ such that for every $\varepsilon>0$ one can find $a'>a$ and $b'_1<\dots<b'_k$ in $\Gamma_{a'}$ with
--
--   $$\max\big(|a-a'|,|b_1-b'_1|,\dots,|b_k-b'_k|\big)<\varepsilon,$$
--
--   and also $a''<a$ and $b''_1<\dots<b''_k$ in $\Gamma_{a''}$ with $\max(|a-a''|,|b_1-b''_1|,\dots,|b_k-b''_k|)<\varepsilon$.
--
--   No measurability of $\Gamma$ is assumed. The lemma is the device by which forbidden configurations on a set of full measure become bounds on the number of points in its fibres.
--
--   **Formalization Note** $|\Gamma_a|$ is the cardinality in $\mathbb N\cup\{\infty\}$; $b$, $b'$, $b''$ are strictly increasing $k$-tuples; the maximum is written as a conjunction of the $k+1$ bounds. The same $a$ and $b$ serve both directions.
-- source:
--   arXiv:1208.1509v2, Lemma 3.2, p. 19

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Abs

open MeasureTheory

theorem lemma_3_2 (k : ℕ) (hk : 0 < k) (Γ : Set (ℝ × ℝ))
    (hunc : ¬ {a : ℝ | (k : ℕ∞) ≤ {y : ℝ | (a, y) ∈ Γ}.encard}.Countable) :
    ∃ (a : ℝ) (b : Fin k → ℝ), StrictMono b ∧ (∀ i, (a, b i) ∈ Γ) ∧
      ∀ ε : ℝ, 0 < ε →
        (∃ a' : ℝ, a < a' ∧ ∃ b' : Fin k → ℝ, StrictMono b' ∧ (∀ i, (a', b' i) ∈ Γ) ∧
          |a - a'| < ε ∧ ∀ i, |b i - b' i| < ε) ∧
        (∃ a'' : ℝ, a'' < a ∧ ∃ b'' : Fin k → ℝ, StrictMono b'' ∧ (∀ i, (a'', b'' i) ∈ Γ) ∧
          |a - a''| < ε ∧ ∀ i, |b i - b'' i| < ε) := by sorry

end MartOT.Abs
