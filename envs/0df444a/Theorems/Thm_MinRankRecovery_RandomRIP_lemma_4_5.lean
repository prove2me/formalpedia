-- Prove2me | Theorems.Thm_MinRankRecovery_RandomRIP_lemma_4_5
-- name    : MinRankRecovery.RandomRIP.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:38.243497+00:00
-- url     : https://prove2.me/theorems/5f6b3bde-b106-4475-a2f5-851489375631
-- title:
--   Lemma 4.5 — covering number of Σ_mnr: 𝔑(ε) ≤ (2C₀/ε)^{r(m+n−2r)} for 0 < ε ≤ 1
-- statement:
--   For subspaces $V\subseteq\mathbb R^m$ and $W\subseteq\mathbb R^n$ of dimension $r$, let $\Sigma(V,W)$ be the subspace of $m\times n$ matrices with column space in $V$ and row space in $W$, and let $\Sigma_{mnr}$ be the family of all such subspaces. The **covering number** $\mathfrak N(\epsilon)$ of $\Sigma_{mnr}$ is the smallest number of pairs $(V_i,W_i)$ such that every pair $(V,W)$ has some $i$ with $\rho(\Sigma(V,W),\Sigma(V_i,W_i))\le\epsilon$.
--
--   There is a constant $C_0>0$, independent of $\epsilon$, $m$, $n$ and $r$, such that for all $r\le\min(m,n)$ and all $0<\epsilon\le 1$,
--   $$\mathfrak N(\epsilon)\le\Big(\frac{2C_0}{\epsilon}\Big)^{r(m+n-2r)}.$$
--
--   Since a matrix of rank at most $r$ lies in some $\Sigma(V,W)$, this lemma, combined with the stability of near isometry under perturbation of the subspace, reduces the restricted isometry property to finitely many subspaces.
--
--   **Formalization Note** The bound on the minimum is stated equivalently as the existence of a net: there are $N\le(2C_0/\epsilon)^{r(m+n-2r)}$ pairs $(V_i,W_i)$ of $r$-dimensional subspaces such that every pair of $r$-dimensional subspaces is within $\rho$-distance $\epsilon$ of one of them. The constant $C_0$ is quantified before $m,n,r,\epsilon$. **Correction:** the paper states no range for $\epsilon$; the statement is posed for $0<\epsilon\le1$, because for $\epsilon>2C_0$ the right side is below $1$ while $\mathfrak N(\epsilon)\ge1$, so the printed bound fails for large $\epsilon$. The paper only uses $\epsilon<\delta/4<1$. The natural-number exponent $r(m+n-2r)$ involves no truncation since $r\le m$ and $r\le n$.
-- source:
--   Recht, Fazel & Parrilo, arXiv:0706.4138v1, Lemma 4.5, (4.16), p. 18; covering number defined on p. 17

import Mathlib
import Definitions.Def_MinRankRecovery_RandomRIP_SubspaceDist

namespace MinRankRecovery.RandomRIP

/-- Lemma 4.5, p. 18, for resolutions `0 < ε ≤ 1`: there is a constant `C₀ > 0`, independent of
`ε, m, n, r`, such that the set `Σ_{mnr}` of subspaces `Σ(V, W)` (`dim V = dim W = r`) has an
`ε`-net, in the distance `ρ`, of at most `(2C₀/ε)^{r(m+n−2r)}` subspaces `Σ(Vᵢ, Wᵢ)` with
`dim Vᵢ = dim Wᵢ = r`; i.e. the covering number satisfies `𝔑(ε) ≤ (2C₀/ε)^{r(m+n−2r)}`. -/
theorem lemma_4_5 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ m n r : ℕ, r ≤ m → r ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ N : ℕ, ∃ V' : Fin N → Submodule ℝ (EuclideanSpace ℝ (Fin m)),
        ∃ W' : Fin N → Submodule ℝ (EuclideanSpace ℝ (Fin n)),
        (N : ℝ) ≤ (2 * C₀ / ε) ^ (r * (m + n - 2 * r)) ∧
        (∀ i, Module.finrank ℝ (V' i) = r ∧ Module.finrank ℝ (W' i) = r) ∧
        ∀ (V : Submodule ℝ (EuclideanSpace ℝ (Fin m)))
          (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))),
          Module.finrank ℝ V = r → Module.finrank ℝ W = r →
          ∃ i, projDist (sigmaSub V W) (sigmaSub (V' i) (W' i)) ≤ ε := by sorry

end MinRankRecovery.RandomRIP
