-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_corollary_24
-- name    : GaussLocalMaxColoring.Main.corollary_24
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:22:27.803288+00:00
-- url     : https://prove2.me/theorems/2e8d1d12-8496-49d0-93f8-0083feea3e9f
-- title:
--   Corollary 24 — $\{u_y\}_{y\in W_0}$ is a $(U_0t,\,1-O(te^{-t^2/4}))$-cover
-- statement:
--   There are absolute constants $K>0$ and $t_0$ such that: for every strict vector 3-coloring $\{v_x\}$ of a graph $G$, every vertex set $F$ (the core $F_{\ell-1}$), every root $r\in F$ and every $t\ge t_0$, if $p_F(r)\le e^{-t^2/2}$ then $\{u_y\}_{y\in W_0}$, $W_0=N_F(r)$, $u_y=v_y-\langle v_r,v_y\rangle v_r$, is a $(U_0t,\,1-Kte^{-t^2/4})$-cover, $U_0=3/(2\sqrt2)$: $\mathbb P_g[\max_{y\in W_0}\langle g,u_y\rangle\ge U_0t]\ge1-Kte^{-t^2/4}$.
--
--   Differences from the source:
--   - generalization: the cores F_{ℓ−1} ⊇ F_ℓ of Algorithm 2, a root r ∈ F_ℓ, t = √(2 log(1/δ)) of Table 2 → any vertex set F, any r ∈ F, any real t ≥ t₀; reason: the proof uses only p_F(r) ≤ e^{−t²/2} (Lemma 23 with a = √(3/2)t); the paper's instances are covered
--   - reading: 1 − O(t e^{−t²/4}) → ∃ K > 0 and t₀, fixed before every graph, vector family, F, r and t, with covering probability 1 − K t e^{−t²/4} for t ≥ t₀; reason: O(·) as t → ∞ with an absolute constant
--   - encoding: the family {u_y}_{y∈W₀}; an (s, q)-cover P_g[max ⟨g, z⟩ ≥ s] ≥ q → the Finset image of u over N_F(r), the published IsCover (≥ at the threshold); reason: repeated vectors do not change the maximum
--   - encoding: vertex set V with a fixed total order breaking ties → V = Fin n with its order; reason: Lean convention; every finite ordered vertex set is relabelled this way
--   - encoding: vectors in R^d, g ∼ N(0, I_d), P_g → Space d = EuclideanSpace ℝ (Fin d), any d, Mathlib stdGaussian (gaussProb); reason: Lean convention; same instances
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Corollary 24, printed p. 20 (PDF 22)

import Mathlib
import Definitions.Def_RecGaussColoring_Main_Rounding
import Definitions.Def_GaussLocalMaxColoring_Main_Section5

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical

namespace GaussLocalMaxColoring.Main

/-- **Corollary 24** (p. 20, PDF 22). There are absolute constants `K > 0` and `t₀` (the `O` of
`1 − O(t e^{−t²/4})`) such that: for every strict vector 3-coloring `{v_x}` of a graph `G`, every
vertex set `F` (the core `F_{ℓ−1}`), every root `r ∈ F` and every `t ≥ t₀`, if
`p_F(r) ≤ e^{−t²/2}` then `{u_y}_{y ∈ W₀}`, `W₀ = N_F(r)`, `u_y = v_y − ⟨v_r, v_y⟩ v_r`, is a
`(U₀ t, 1 − K t e^{−t²/4})`-cover, `U₀ = 3/(2√2)`. -/
theorem corollary_24 :
    ∃ K t₀ : ℝ, 0 < K ∧
      ∀ {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → Space d),
        StrictVectorColoring G v → ∀ (F : Finset (Fin n)) (r : Fin n), r ∈ F →
        ∀ t : ℝ, t₀ ≤ t → pLocal G v F r ≤ Real.exp (-(t ^ 2 / 2)) →
          IsCover ((nbr G F r).image (uvec v r)) (U0 * t)
            (1 - K * t * Real.exp (-(t ^ 2 / 4))) := by sorry

end GaussLocalMaxColoring.Main
