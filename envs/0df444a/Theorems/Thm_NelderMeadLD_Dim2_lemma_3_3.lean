-- Prove2me | Theorems.Thm_NelderMeadLD_Dim2_lemma_3_3
-- name    : NelderMeadLD.Dim2.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:14:33.043219+00:00
-- url     : https://prove2.me/theorems/3cdb860d-8551-4e5e-bbe1-d2c60fc7a931
-- title:
--   Lemma 3.3, p. 121 — f bounded below: f₁ converges; nonshrink steps decrease values; limits f*ᵢ exist and are ordered after the last shrink; vertices converge if only shrinks
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ ($n\ge1$) be bounded below, let the coefficients satisfy (2.1), and let $\Delta_0,\Delta_1,\dots$ be a run of Algorithm NM on $f$ from a nondegenerate initial simplex $\Delta_0$. Write $f_i^{(k)}=f(x_i^{(k)})$. Then:
--   1. the sequence $(f_1^{(k)})_k$ converges;
--   2. at every nonshrink iteration $k$,
--   $$f_i^{(k+1)}\le f_i^{(k)}\quad(1\le i\le n+1),$$
--   with strict inequality for at least one $i$;
--   3. if no shrink occurs from iteration $K_0$ on, then there are numbers $f_1^*,\dots,f_{n+1}^*$ such that (i) $f_i^{(k)}\to f_i^*$ for every $i$, (ii) $f_i^*\le f_i^{(k)}$ for every $i$ and every $k\ge K_0$, and (iii) $f_1^*\le f_2^*\le\dots\le f_{n+1}^*$;
--   4. if every iteration from $K_0$ on is a shrink, then all vertices converge to one common point.
--
--   These are the basic monotonicity and convergence facts on which the analysis of limiting vertex values rests.
--
--   **Formalization Note** "Finitely many shrink (resp. nonshrink) iterations" is written as the existence of $K_0$ after which none occurs. Part 3(ii) is printed "for all $k$"; it is false when a shrink precedes $K_0$, because a shrink can raise vertex values. A counterexample with $n=1$, $\rho=1$, $\gamma=\sigma=\tfrac12$: $f(0)=0$, $f(1)=1$, $f(\tfrac12)=5$, $f(x)=2+|x|$ otherwise, start $(0,1)$; iteration 0 shrinks to $(0,\tfrac12)$ and afterwards $f_2^{(k)}\to2>f_2^{(0)}=1$. The statement therefore asserts (ii) for $k\ge K_0$, which is what the later proofs use. Vertex $x_i$ is 0-based index $i-1$.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 121, Lemma 3.3

import Mathlib
import Definitions.Def_NelderMeadLD_Dim2_Algorithm
open Filter Topology

namespace NelderMeadLD.Dim2

theorem lemma_3_3 {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ) (hnd : Nondegenerate (Δ 0))
    (hbdd : BddBelow (Set.range f)) :
    (∃ L : ℝ, Tendsto (fun k => f (Δ k 0)) atTop (𝓝 L)) ∧
    (∀ k, ¬ IsShrinkAt f ρ χ γ Δ k →
      (∀ i, f (Δ (k + 1) i) ≤ f (Δ k i)) ∧ ∃ i, f (Δ (k + 1) i) < f (Δ k i)) ∧
    (∀ K₀ : ℕ, (∀ k ≥ K₀, ¬ IsShrinkAt f ρ χ γ Δ k) →
      ∃ fstar : Fin (n + 1) → ℝ,
        (∀ i, Tendsto (fun k => f (Δ k i)) atTop (𝓝 (fstar i))) ∧
        (∀ i, ∀ k ≥ K₀, fstar i ≤ f (Δ k i)) ∧
        Monotone fstar) ∧
    (∀ K₀ : ℕ, (∀ k ≥ K₀, IsShrinkAt f ρ χ γ Δ k) →
      ∃ p : E n, ∀ i, Tendsto (fun k => Δ k i) atTop (𝓝 p)) := by sorry

end NelderMeadLD.Dim2
