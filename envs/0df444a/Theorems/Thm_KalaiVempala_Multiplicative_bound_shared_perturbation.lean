-- Prove2me | Theorems.Thm_KalaiVempala_Multiplicative_bound_shared_perturbation
-- name    : KalaiVempala.Multiplicative.bound_shared_perturbation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:32.673995+00:00
-- url     : https://prove2.me/theorems/14f1b5c4-5dcb-47dc-8a79-b9ec26c63972
-- title:
--   Proof of Thm 1.1(b), p. 303 — Σ M(s_{1:t}+p₁)·s_t ≤ M(s_{1:T})·s_{1:T} + D|p₁|_∞
-- statement:
--   Let $\mathcal D \subset \mathbb R^n$ be a decision set whose $\ell_1$-diameter is at most $D$, i.e. $|d - d'|_1 \le D$ for all $d, d' \in \mathcal D$, and let $M$ be an argmin oracle for $\mathcal D$. For every state sequence $s_1, \dots, s_T \in \mathbb R^n$ and every fixed perturbation vector $p_1 \in \mathbb R^n$,
--   $$\sum_{t=1}^T M(s_{1:t} + p_1)\cdot s_t \;\le\; M(s_{1:T})\cdot s_{1:T} + D\,|p_1|_\infty .$$
--
--   This is the "be the perturbed leader" bound with one perturbation shared by all periods, the special case $p_t = p_1$ of Lemma 3.1 of the paper. It is the deterministic half of the proof of Theorem 1.1(b): the perturbation costs at most $D$ times its sup norm.
--
--   **Formalization Note** $|p_1|_\infty$ is the Lean norm `‖p₁‖`, which on `Fin n → ℝ` is the sup norm. The bound holds for arbitrary real states; the set $\mathcal S$, the nonnegativity of $\mathcal D$ and $\mathcal S$, and the parameters $R$, $A$ are not used and are not hypotheses.
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 303, proof of Theorem 1.1(b), first display (by Lemma 3.1, p. 300)

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Multiplicative_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Multiplicative

theorem bound_shared_perturbation {n : ℕ} (Dset : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : KalaiVempala.Additive.IsArgminOracle Dset M)
    (Ddiam : ℝ) (hD : ∀ d ∈ Dset, ∀ d' ∈ Dset, ∑ i, |d i - d' i| ≤ Ddiam)
    (s : ℕ → Fin n → ℝ) (T : ℕ) (p₁ : Fin n → ℝ) :
    ∑ t ∈ Finset.Icc 1 T, M (prefixSum s t + p₁) ⬝ᵥ s t ≤
      M (prefixSum s T) ⬝ᵥ prefixSum s T + Ddiam * ‖p₁‖ := by sorry

end KalaiVempala.Multiplicative
