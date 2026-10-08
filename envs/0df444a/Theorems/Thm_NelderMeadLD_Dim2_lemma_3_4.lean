-- Prove2me | Theorems.Thm_NelderMeadLD_Dim2_lemma_3_4
-- name    : NelderMeadLD.Dim2.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:14:44.205721+00:00
-- url     : https://prove2.me/theorems/771aec3c-408d-4054-85b8-f06890fb21eb
-- title:
--   Lemma 3.4, pp. 121–122 — broken convergence: if f*ⱼ < f*ⱼ₊₁ then the first j vertices are eventually fixed
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ ($n\ge1$) be bounded below, let the coefficients satisfy (2.1), and let $(\Delta_k)$ be a run of Algorithm NM on $f$ from a nondegenerate initial simplex in which no shrink step occurs. Suppose that for some $j$ with $1\le j\le n$ the limits $f_j^*=\lim_k f_j^{(k)}$ and $f_{j+1}^*=\lim_k f_{j+1}^{(k)}$ satisfy
--   $$f_j^*<f_{j+1}^*\qquad(3.2).$$
--   Then there is $K$ such that for all $k\ge K$ the change index satisfies $k^*>j$, i.e.
--   $$x_i^{(k+1)}=x_i^{(k)}\qquad\text{for } 1\le i\le j \text{ and all } k\ge K.$$
--
--   Property (3.2) is called *broken convergence* for vertex $j$; the lemma says it freezes the $j$ best vertices.
--
--   **Formalization Note** The paper's index $j\in\{1,\dots,n\}$ is a Lean `j : Fin n` with `j.val` $=j-1$, so $x_j$ is `j.castSucc` and $x_{j+1}$ is `j.succ`; "the first $j$ vertices" are the indices `i ≤ j.castSucc`. The limits $f_j^*$, $f_{j+1}^*$ are taken as hypotheses (`Tendsto … (𝓝 a)`, `Tendsto … (𝓝 b)`, `a < b`); their existence is Lemma 3.3 (3). The change index $k^*>j$ is stated through its meaning (2.8): the first $j$ vertices do not change.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), pp. 121–122, Lemma 3.4, (3.2)–(3.3)

import Mathlib
import Definitions.Def_NelderMeadLD_Dim2_Algorithm
open Filter Topology

namespace NelderMeadLD.Dim2

theorem lemma_3_4 {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ) (hnd : Nondegenerate (Δ 0))
    (hbdd : BddBelow (Set.range f)) (hnoshrink : ∀ k, ¬ IsShrinkAt f ρ χ γ Δ k)
    (j : Fin n) (a b : ℝ)
    (ha : Tendsto (fun k => f (Δ k j.castSucc)) atTop (𝓝 a))
    (hb : Tendsto (fun k => f (Δ k j.succ)) atTop (𝓝 b)) (hab : a < b) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ i : Fin (n + 1), i ≤ j.castSucc → Δ (k + 1) i = Δ k i := by sorry

end NelderMeadLD.Dim2
