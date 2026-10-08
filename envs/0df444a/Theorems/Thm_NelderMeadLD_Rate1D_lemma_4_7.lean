-- Prove2me | Theorems.Thm_NelderMeadLD_Rate1D_lemma_4_7
-- name    : NelderMeadLD.Rate1D.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:51.279793+00:00
-- url     : https://prove2.me/theorems/4f74029f-4a42-4526-9bd3-332d2cf474cb
-- title:
--   Lemma 4.7, p. 132 — with ρ = 1, after a contraction there are never more than j* consecutive expansions
-- statement:
--   Let $f:\mathbb R \to \mathbb R$ be strictly convex with bounded level sets, and apply the one-dimensional Nelder–Mead method with $\rho = 1$, $\chi > 1$, $0 < \gamma < 1$, $0 < \sigma < 1$ to $f$, starting from a nondegenerate ordered initial interval $\Delta_0$. Let $N_{NM} = \max(\chi, 1/\gamma)$ and let $j^*$ be the largest integer $j \ge 0$ with
--   $$\chi + \chi^2 + \cdots + \chi^{j} < N_{NM}$$
--   (so $j^* = 0$ when $\chi = N_{NM}$). If iteration $k$ is a contraction, then at all later iterations there are no more than $j^*$ consecutive expansions: whenever $m > k$ and iterations $m, m+1, \dots, m+L-1$ are all expansions, $L \le j^*$.
--
--   Together with Lemma 4.6 this bounds the length of every move sequence between two contractions, which is what makes the diameter decrease at a uniform rate.
--
--   **Formalization Note.** $\rho = 1$ is substituted; (2.1) is carried as a hypothesis. The two cases (a) and (b) of the page are encoded by one definition of $j^*$ as the largest $j$ in $\{0, \dots, \lceil N_{NM}\rceil\}$ satisfying the strict inequality; in case (a) only $j = 0$ satisfies it. The block of expansions may start at any $m > k$, not only at $k + 1$.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 132, Lemma 4.7

import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm
import Definitions.Def_NelderMeadLD_Rate1D_Algorithm

namespace NelderMeadLD.Rate1D

open NelderMeadLD.Conv1D

theorem lemma_4_7 (χ γ σ : ℝ) (hpar : ParamsOK 1 χ γ σ)
    (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ})
    (p0 : ℝ × ℝ) (h0 : IsStart f p0)
    (k : ℕ) (hk : IsContraction (moveAt f χ γ σ p0 k)) :
    ∀ m : ℕ, k < m → ∀ L : ℕ,
      (∀ i < L, moveAt f χ γ σ p0 (m + i) = Move.expand) → L ≤ jStar χ γ := by sorry

end NelderMeadLD.Rate1D
