-- Prove2me | Theorems.Thm_KangKurtz_SCC_no_repeat
-- name    : KangKurtz.SCC.no_repeat
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:47:59.104998+00:00
-- url     : https://prove2.me/theorems/11fc4e84-1efd-48ee-a765-df4cd53c7624
-- title:
--   Proof of Lemma 3.4, p. 16 — a chain cannot revisit a component
-- statement:
--   Let $\theta=\sum_j\theta^j$ be the component decomposition of Lemma 3.4. Suppose a finite sequence of pieces $\theta^{j_0},\ldots,\theta^{j_n}$ is selected as in its proof: at each step, a reaction decreases the preceding piece and increases the next piece, its exponent equals the maxima on both sign sets of the preceding piece, and that exponent does not exceed the positive-set maximum of the next piece. Then
--
--   $$j_a=j_b\quad\Longrightarrow\quad a=b.$$
--
--   This is the no-repetition claim used in the proof of Lemma 3.4 to bound the length of the component chain.
--
--   **Formalization Note** The chain carries the maximum equalities and inequality of the paper's selection procedure. The paper's standing nonnegative scaling and binary-consumption assumptions remain explicit.
-- source:
--   Kang and Kurtz, Separation of time-scales and model reduction for stochastic reaction networks, arXiv:1011.1672v1, p. 16, §3.4, proof of Lemma 3.4, no-repetition claim

import Mathlib
import Definitions.Def_KangKurtz_SCC_Setting

namespace KangKurtz.SCC

theorem no_repeat
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
      θs j i ≠ 0 → θs j' i' ≠ 0 → ¬ SameComp ν ν' i i')
    {n : ℕ} (jj : Fin (n + 1) → Fin m) (l : Fin n → Fin r)
    (hchain : ∀ t : Fin n,
      l t ∈ GammaMinus ν ν' (θs (jj (Fin.castSucc t))) ∧
      l t ∈ GammaPlus ν ν' (θs (jj (Fin.succ t))) ∧
      maxRho ν α β (GammaPlus ν ν' (θs (jj (Fin.castSucc t)))) =
        maxRho ν α β (GammaMinus ν ν' (θs (jj (Fin.castSucc t)))) ∧
      maxRho ν α β (GammaMinus ν ν' (θs (jj (Fin.castSucc t)))) =
        (rho ν α β (l t) : WithBot ℝ) ∧
      (rho ν α β (l t) : WithBot ℝ) ≤
        maxRho ν α β (GammaPlus ν ν' (θs (jj (Fin.succ t))))) :
    Function.Injective jj := by sorry
end KangKurtz.SCC
