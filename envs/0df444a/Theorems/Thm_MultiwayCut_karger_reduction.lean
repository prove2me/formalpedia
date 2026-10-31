-- Prove2me | Theorems.Thm_MultiwayCut_karger_reduction
-- name    : MultiwayCut.karger_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:41.059591+00:00
-- url     : https://prove2.me/theorems/51889ea1-77d3-4eb6-97a9-55257c979f14
-- title:
--   p.4 — cut density $\gamma$ gives approximation $\gamma$ (corrected: uniform $O(\varepsilon^2)$ remainder instead of $\limsup$)
-- statement:
--   The paper states (p.4): "As in Karger et al. [21], it is easy to show that any randomized algorithm for Multiway Cut achieves an approximation of $\gamma=\max_{1\le i<j\le k}\gamma_{i,j}$." With the $\limsup$ cut density of Definition 2.1 this is false; the following corrected form holds.
--
--   Let $s(\mathbf u,\mathbf v)$ be a function on $\Delta_k\times\Delta_k$ with $s(\mathbf u,\mathbf u)=0$, $s(\mathbf u,\mathbf v)=s(\mathbf v,\mathbf u)$ and $s(\mathbf u,\mathbf w)\le s(\mathbf u,\mathbf v)+s(\mathbf v,\mathbf w)$; every separation probability $\Pr[g(\mathbf u)\ne g(\mathbf v)]$ of a randomized labeling has these properties (the third is the union bound). Let $\gamma\in\mathbb R$ and suppose there is a constant $C$ such that for every $(i,j)$-edge $(\mathbf u,\mathbf v)$ with parameter $\varepsilon$, in any order of the coordinates and for any $i<j$,
--   $$s(\mathbf u,\mathbf v)\le\gamma\,\varepsilon+C\varepsilon^2 .$$
--   Then
--   1. $s(\mathbf u,\mathbf v)\le\gamma\cdot\frac12\|\mathbf u-\mathbf v\|_1$ for all $\mathbf u,\mathbf v\in\Delta_k$;
--   2. for every instance and every feasible embedding $x$ of the simplex relaxation,
--   $$\sum_{e=(u,v)\in E}w_e\,s(x_u,x_v)\le\gamma\sum_{e=(u,v)\in E}w_e\,\tfrac12\|x_u-x_v\|_1 ,$$
--   i.e. the expected weight of the cut is at most $\gamma$ times the relaxation's objective.
--
--   Differences from the source:
--   - correction: cut density $\gamma_{i,j}$ defined by $\limsup_{\varepsilon\to0}\Pr[g(u)\ne g(v)]/\varepsilon$ → a bound $s\le\gamma\varepsilon+C\varepsilon^2$ on every $(i,j)$-edge, with $C$ independent of the edge; reason: the printed statement is false: for $k=2$ the deterministic labeling $g(u)=1$ iff $u_1=1$ or $u_1\in[0.6,0.7)$ (else $2$) labels the terminals correctly and has $\gamma_{1,2}=0$, yet on the unit-weight path $t_1,a,b,c,t_2$ with $a,b,c$ at $u_1=0.75,0.65,0.55$ (an optimal relaxation solution of value $1$) it cuts $3$ edges
--   - generalization: a randomized algorithm (a distribution over labelings) → any function $s$ on $\Delta_k\times\Delta_k$ vanishing on the diagonal, symmetric and satisfying the triangle inequality; reason: every separation probability $\Pr[g(u)\ne g(v)]$ has these properties, so the statement specializes to the paper's
--   - reading: "achieves an approximation of $\gamma$" → the expected cut weight is at most $\gamma$ times the relaxation objective of every feasible embedding (and the pointwise bound $s\le\gamma\frac12\|u-v\|_1$); reason: this is the guarantee the paper derives from cut density; at an optimal embedding the objective is at most the optimum cut
--   - encoding: expected weight of the cut → $\sum_{e\in E}w_e\,s(x_u,x_v)$; reason: linearity of expectation
-- source:
--   Buchbinder, Schwartz & Weizman, Simplex Transformations and the Multiway Cut Problem, manuscript of Nov. 1, 2016, p.4 (§2.4, "As in Karger et al. [21], it is easy to show that any randomized algorithm for Multiway Cut achieves an approximation of γ = max γ_{i,j}")

import Mathlib
import Definitions.Def_MultiwayCut_Instance
import Definitions.Def_MultiwayCut_CutDensity

namespace MultiwayCut

/-- **Cut density bounds the approximation ratio** (corrected), Buchbinder, Schwartz & Weizman,
*Simplex Transformations and the Multiway Cut Problem*, manuscript of Nov. 1, 2016, p.4: "As in
Karger et al. [21], it is easy to show that any randomized algorithm for Multiway Cut achieves
an approximation of `γ = max_{1≤i<j≤k} {γ_{i,j}}`."

Corrected form. Let `s u v` be the probability `Pr[g(u) ≠ g(v)]` that a randomized labeling
separates `u` and `v`; it vanishes on the diagonal, is symmetric and obeys the union bound
`s u w ≤ s u v + s v w` on `Δ_k` (every separation probability does). If on every `(i, j)`-edge
(any order `π`, any `i < j`) with parameter `ε` the separation probability is at most
`γ ε + C ε²` for one constant `C` independent of the edge, then `s u v ≤ γ · ½ ‖u − v‖₁` for all
`u, v ∈ Δ_k`, and hence the expected weight of the cut is at most `γ` times the relaxation's
objective on every instance and every feasible embedding.

**Formalization Note.** The printed statement uses the lim sup cut density of Definition 2.1,
under which it is false (a deterministic `k = 2` labeling of density `0` that cuts `3` edges of
an optimal path solution of value `1`; see the natural-language statement); the
uniform second-order remainder `C ε²` is the correction. `γ` bounds every `γ_{i,j}`. The
expected cut weight is `Σ_{e∈E} w_e · s(x_u, x_v)` by linearity of expectation. -/
theorem karger_reduction {k : ℕ} (s : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (γ : ℝ)
    (hdiag : ∀ u ∈ stdSimplex ℝ (Fin k), s u u = 0)
    (hsymm : ∀ u ∈ stdSimplex ℝ (Fin k), ∀ v ∈ stdSimplex ℝ (Fin k), s u v = s v u)
    (htri : ∀ u ∈ stdSimplex ℝ (Fin k), ∀ v ∈ stdSimplex ℝ (Fin k),
      ∀ w ∈ stdSimplex ℝ (Fin k), s u w ≤ s u v + s v w)
    (hedge : ∃ C : ℝ, ∀ (π : Equiv.Perm (Fin k)) (i j : Fin k) (ε : ℝ) (u v : Fin k → ℝ),
      IsIJEdge π i j ε u v → s u v ≤ γ * ε + C * ε ^ 2) :
    (∀ u ∈ stdSimplex ℝ (Fin k), ∀ v ∈ stdSimplex ℝ (Fin k), s u v ≤ γ * halfL1 u v) ∧
    ∀ {V : Type} [Fintype V] (I : Instance V k) (x : V → Fin k → ℝ),
      IsFeasibleEmbedding I x →
        ∑ e ∈ I.E, I.w e * s (x e.1) (x e.2) ≤ γ * relaxValue I x := by sorry

end MultiwayCut
