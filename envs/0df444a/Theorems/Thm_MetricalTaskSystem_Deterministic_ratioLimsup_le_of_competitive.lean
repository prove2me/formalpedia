-- Prove2me | Theorems.Thm_MetricalTaskSystem_Deterministic_ratioLimsup_le_of_competitive
-- name    : MetricalTaskSystem.Deterministic.ratioLimsup_le_of_competitive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:11:46.880985+00:00
-- url     : https://prove2.me/theorems/1d638a2c-5da9-4ef2-876a-6eca5f0734a5
-- title:
--   Lemma 2.1 — $w(A)\ge w_{\mathbf T}(A)$ when $c_0(T^1\cdots T^m)\to\infty$
-- statement:
--   Let $(S,d)$ be a task system, $A$ an on-line algorithm, $s_0$ an initial state, and $\mathbf T=T^1T^2\cdots$ an infinite sequence of nonnegative tasks such that the off-line costs $c_0(T^1\cdots T^m)$ tend to $+\infty$ as $m\to\infty$. Then every $w$ for which $A$ is $w$-competitive satisfies
--   $$w_{\mathbf T}(A)=\limsup_{m\to\infty}\frac{c_A(T^1\cdots T^m)}{c_0(T^1\cdots T^m)}\le w .$$
--   Equivalently, $w(A)=\inf\{w: A\text{ is }w\text{-competitive}\}\ge w_{\mathbf T}(A)$.
--
--   This lemma turns the analysis of a single adversarial infinite sequence into a lower bound on the competitive ratio of $A$.
--
--   **Formalization Note** The limsup is in `EReal`; the statement is phrased for each $w\in W_A$, which is equivalent to the paper's with $\inf\emptyset=+\infty$.
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), p. 749, Lemma 2.1

import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_CruelTaskmaster

namespace MetricalTaskSystem.Deterministic

/-- **Lemma 2.1** (Borodin–Linial–Saks 1992, p. 749). If `T` is an infinite (nonnegative) task
sequence whose off-line costs `c₀(T¹ ⋯ Tᵐ)` tend to infinity, then `w_T(A) ≤ w` for every
`w ∈ W_A`; that is, `w(A) = inf W_A ≥ w_T(A)`. -/
theorem ratioLimsup_le_of_competitive {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (A : OnlineAlgorithm S) (s₀ : S)
    (T : ℕ → S → ℝ) (hT : ∀ i s, 0 ≤ T i s)
    (hT_inf : Filter.Tendsto (fun m : ℕ => offlineOpt d s₀ (prefixSeq T m))
      Filter.atTop Filter.atTop)
    (w : ℝ) (hw : IsCompetitive d A w) :
    ratioLimsup d A s₀ T ≤ (w : EReal) := by sorry

end MetricalTaskSystem.Deterministic
