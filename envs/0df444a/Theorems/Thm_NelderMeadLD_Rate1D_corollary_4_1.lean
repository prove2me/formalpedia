-- Prove2me | Theorems.Thm_NelderMeadLD_Rate1D_corollary_4_1
-- name    : NelderMeadLD.Rate1D.corollary_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:17.753973+00:00
-- url     : https://prove2.me/theorems/fab1dd7d-0b82-4dfd-a4ea-c776cfe8c295
-- title:
--   Corollary 4.1, p. 131 — with ρ = 1, a contraction occurs no later than iteration K + r*, K the first bracketing index
-- statement:
--   Let $f:\mathbb R \to \mathbb R$ be strictly convex with bounded level sets, and apply the one-dimensional Nelder–Mead method with $\rho = 1$, $\chi > 1$, $0 < \gamma < 1$, $0 < \sigma < 1$ to $f$, starting from a nondegenerate ordered initial interval $\Delta_0$. Let $K$ be the iteration index of Lemma 4.2, at which for the first time
--   $$f_1^{(K)} \le f_e^{(K)},$$
--   where $f_1^{(K)}$ is the value at the best vertex of $\Delta_K$ and $f_e^{(K)}$ the value at the expansion point $x_e^{(K)} = x_1^{(K)} + \chi(x_1^{(K)} - x_2^{(K)})$. Then some iteration $k$ with $K \le k \le K + r^*$, where $r^* = \lceil \chi - 1\rceil$, is a contraction (outside or inside).
--
--   The result locates the first contraction after the minimizer is bracketed; from that contraction on, the paper's move-sequence analysis applies.
--
--   **Formalization Note.** The printed corollary names only $\rho = 1$; the conditions $\chi > 1$, $0 < \gamma < 1$ (and $0 < \sigma < 1$) are the section's standing assumptions (2.1) and are carried as hypotheses. $K$ is a binder together with the hypothesis that it is the *first* index with $f_1^{(K)} \le f_e^{(K)}$, as on the page.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 131, Corollary 4.1

import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm
import Definitions.Def_NelderMeadLD_Rate1D_Algorithm

namespace NelderMeadLD.Rate1D

open NelderMeadLD.Conv1D

theorem corollary_4_1 (χ γ σ : ℝ) (hpar : ParamsOK 1 χ γ σ)
    (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ})
    (p0 : ℝ × ℝ) (h0 : IsStart f p0)
    (K : ℕ) (hK : FirstBracket f χ γ σ p0 K) :
    ∃ k : ℕ, K ≤ k ∧ k ≤ K + rStar χ ∧ IsContraction (moveAt f χ γ σ p0 k) := by sorry

end NelderMeadLD.Rate1D
