-- Prove2me | Theorems.Thm_HolleyLiggett_Duality_eq_2_5
-- name    : HolleyLiggett.Duality.eq_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:40:42.206253+00:00
-- url     : https://prove2.me/theorems/bf0dd51a-5cdd-4cce-8cf5-a90111fd26f6
-- title:
--   (2.5), p. 647 — first-step decomposition of the b.p.i.: P_F(A_{n+1} ∩ C(η) = ∅) = Σ P_{⋃ N_{i,k_i}}(A_n ∩ C(η) = ∅) ∏ f_i(k_i)
-- statement:
--   Let $A_n$ be the discrete-time branching process with interference determined by $\{N_{i,k}\}$ (with $N_{i,0}=\emptyset$) and $\{f_i\}$ on a countable site set $I$. For every $n\ge0$, every configuration $\eta\in S$ and every finite $F\subset I$,
--   $$P_F(A_{n+1}\cap C(\eta)=\emptyset)=\sum_{(k_i)_{i\in F}}P_{\bigcup_{i\in F}N_{i,k_i}}(A_n\cap C(\eta)=\emptyset)\,\prod_{i\in F}f_i(k_i),$$
--   the sum over all sequences $(k_i)_{i\in F}$ of nonnegative integers. The factor $\prod_{i\in F}f_i(k_i)$ is the probability that the particle at each $i\in F$ chooses the set $N_{i,k_i}$ at the first step.
--
--   This conditions on the first step of the b.p.i.; it is the b.p.i. half of the induction step in the proof of Theorem (1.6).
--
--   **Formalization Note.** The $n$-step probabilities of the b.p.i. are defined by the last-step recursion $P_F(A_{n+1}=B)=\sum_G P_F(A_n=G)\tilde Q(G,B)$, so this first-step identity is a genuine statement (it is the Chapman–Kolmogorov equation), not an unfolding of the definition.
-- source:
--   Holley and Liggett, Ergodic theorems for weakly interacting infinite systems and the voter model, Ann. Probab. 3 (1975), p. 647, (2.5)

import Mathlib
import Definitions.Def_HolleyLiggett_Duality_Setting

namespace HolleyLiggett.Duality

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- (2.5): `P_F(A_{n+1} ∩ C(η) = ∅) = Σ P_{⋃_{i∈F} N_{i,k_i}}(A_n ∩ C(η) = ∅) P(X_{i,1} = k_i ∀ i ∈ F)`,
the sum over all sequences `(k_i)_{i∈F}`. -/
theorem eq_2_5 {I : Type*} [Countable I] [DecidableEq I] (N : I → ℕ → Finset I)
    (hN0 : ∀ i, N i 0 = ∅) (f : I → PMF ℕ)
    (n : ℕ) (η : Config I) (F : Finset I) :
    dualProb N f (n + 1) F η =
      ∑' k : (↥F → ℕ),
        dualProb N f n (Finset.univ.biUnion (fun i : ↥F => N i (k i))) η * ∏ i : ↥F, f i (k i) := by sorry

end HolleyLiggett.Duality
