-- Prove2me | Theorems.Thm_KangKurtz_SCC_lemma_3_4
-- name    : KangKurtz.SCC.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:47:51.352106+00:00
-- url     : https://prove2.me/theorems/3410c440-8e57-4b25-aebc-4c9f06081efa
-- title:
--   Lemma 3.4, p. 15 — the balance condition passes across components
-- statement:
--   Let $\theta\ge0$ be a species-weight vector and fix a real time-scale exponent $\gamma$. Suppose $\theta=\sum_{j=1}^m\theta^j$, with each nonnegative piece supported in a maximal strongly connected component of the species graph and distinct pieces belonging to distinct components. Then all three assertions of Lemma 3.4 hold:
--
--   $$
--   \begin{aligned}
--   (\forall j,\operatorname{Cond}_{3.2}(\gamma,\theta^j))&\Longrightarrow\operatorname{Cond}_{3.2}(\gamma,\theta),\\
--   (\forall j,\operatorname{Balance}(\theta^j))&\Longrightarrow\operatorname{Balance}(\theta),\\
--   (\forall j,\gamma\le\gamma_{\theta^j})&\Longrightarrow\gamma\le\gamma_\theta.
--   \end{aligned}
--   $$
--
--   The result makes component-level balance checks sufficient for a sum of pieces in different components.
--
--   **Formalization Note** The reaction network follows the paper's standing at-most-binary consumption restriction. The component conditions are stated as support containment within one mutual-reachability class and distinctness of classes. Empty maxima are $-\infty$, and the time-scale bound with no sign-changing reactions is automatically true.
-- source:
--   Kang and Kurtz, Separation of time-scales and model reduction for stochastic reaction networks, arXiv:1011.1672v1, p. 15, §3.4, Lemma 3.4

import Mathlib
import Definitions.Def_KangKurtz_SCC_Setting

namespace KangKurtz.SCC

theorem lemma_3_4
    {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (hbinary : BinaryReactions ν)
    (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i)
    (β : Fin r → ℝ) (γ : ℝ)
    (θ : Fin s → ℝ) (hθ : ∀ i, 0 ≤ θ i)
    {m : ℕ} (θs : Fin m → Fin s → ℝ)
    (hθs : ∀ j i, 0 ≤ θs j i)
    (hsum : θ = ∑ j, θs j)
    (hone : ∀ j i i', θs j i ≠ 0 → θs j i' ≠ 0 → SameComp ν ν' i i')
    (hdist : ∀ j j', j ≠ j' → ∀ i i',
      θs j i ≠ 0 → θs j' i' ≠ 0 → ¬ SameComp ν ν' i i') :
    ((∀ j, Cond32 ν ν' α β γ (θs j)) → Cond32 ν ν' α β γ θ) ∧
    ((∀ j, Balance ν ν' α β (θs j)) → Balance ν ν' α β θ) ∧
    ((∀ j, TimeScale ν ν' α β γ (θs j)) → TimeScale ν ν' α β γ θ) := by sorry
end KangKurtz.SCC
