-- Prove2me | Theorems.Thm_FrechetNearLinear_Main_lemma_4_1
-- name    : FrechetNearLinear.Main.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:36:40.538474+00:00
-- url     : https://prove2.me/theorems/556946b6-9656-4d6d-84f7-13b478267dc1
-- title:
--   Lemma 4.1 — crossing: bi-monotone paths with alternating boundary endpoints intersect; splices stay in F_c; a common point in linear time, a grid point for grid paths
-- statement:
--   Let $R$ be a rectangle of the free-space diagram of $P$ and $Q$. Let $s_1\preceq s_2$ be points of $\mathrm{In}(R)$ and $t_1\preceq t_2$ points of $\mathrm{Out}(R)$ in the boundary orders, and let $\gamma_1$ and $\gamma_2$ be bi-monotone paths in $R$ from $s_1$ to $t_2$ and from $s_2$ to $t_1$. Then
--   $$\exists\,u,v\in[0,1]:\ \gamma_1(u)=\gamma_2(v).$$
--   If moreover both paths lie in $F_c$, then for every common point $\gamma_1(u)=\gamma_2(v)$ there are bi-monotone paths in $R\cap F_c$ from $s_1$ to $t_1$ with point set $\gamma_1[0,u]\cup\gamma_2[v,1]$, and from $s_2$ to $t_2$ with point set $\gamma_2[0,v]\cup\gamma_1[u,1]$ (the splices).
--
--   For polygonal paths a common point can be found in linear time: there are an admissible program $A$ and a constant $C$ such that for all such data where $\gamma_1,\gamma_2$ are polygonal paths given by vertex lists $w_1,w_2$ (input $p[0]=|w_1|$, $p[1]=|w_2|$, memory $w_1$'s coordinates followed by $w_2$'s), $A$ accepts within $C(|w_1|+|w_2|)$ steps with a point $z$ of both paths in $(M[-1],M[-2])$; if both paths have steps in $\{(1,0),(0,1),(1,1)\}$ between grid points, $z$ is a grid point.
--
--   The crossing lemma is why extremal entrances nearly determine reachability through a rectangle; it is used to compile finite summaries (Lemma 4.3).
--
--   **Formalization Note** Paths are Mathlib `Path`s; the boundary order compares positions along the input and output arcs. The machine is the mission's real RAM.
--
--   Differences from the source:
--   - encoding: bi-monotone paths in $R$ → `Path s t` with both coordinates monotone and all values in $R$; reason: Lean convention, same paths
--   - reading: "the bi-monotone paths obtained by splicing them at a common point" → for every common point $\gamma_1(u)=\gamma_2(v)$, a bi-monotone path in $R\cap F_c$ whose point set is $\gamma_1[0,u]\cup\gamma_2[v,1]$ (and the symmetric one); reason: a bi-monotone path is determined up to reparameterization by its point set, which is the splice
--   - reading: "a common point can be found in time linear in their number of segments" → one admissible program on the mission's real RAM, input the two vertex lists, accepting within $C(|w_1|+|w_2|)$ steps with the point in $M[-1],M[-2]$; reason: the paper names no machine; $|w|$ = segments $+1$, so this is $O(\text{segments}+1)$
--   - reading: "For paths with steps in {(1,0),(0,1),(1,1)} between grid points, it can be chosen to be a grid point" → the point the program returns is a grid point when both inputs are grid paths; reason: the stronger of the two readings (it implies that a common grid point exists)
-- source:
--   Huang, Wang, Zhang, Constant Approximation of Fréchet Distance in Near-Linear Time, STOC 2027 submission (manuscript sha256 08be7e65…dd2d), p. 13, Lemma 4.1

import Mathlib
import Definitions.Def_FrechetNearLinear_Main_FreeSpace
import Definitions.Def_FrechetNearLinear_Main_Machine

namespace FrechetNearLinear.Main

/-- Lemma 4.1 (Crossing), p. 13. (i) If `s₁ ⪯ s₂` are input points and `t₁ ⪯ t₂` output points of
`R`, and `γ₁ : s₁ → t₂`, `γ₂ : s₂ → t₁` are bi-monotone paths in `R`, then `γ₁` and `γ₂`
intersect; if both lie in `F_c`, then for every common point `γ₁(u) = γ₂(v)` the splices
`γ₁|[0,u] · γ₂|[v,1] : s₁ → t₁` and `γ₂|[0,v] · γ₁|[u,1] : s₂ → t₂` are bi-monotone paths in
`R ∩ F_c`. (ii) For polygonal paths given by their vertex lists `w₁`, `w₂`, a fixed admissible
program finds a common point within `C · (|w₁| + |w₂|)` steps, and the point it finds is a grid
point whenever both paths are grid paths with steps in `{(1,0), (0,1), (1,1)}`. -/
theorem lemma_4_1 :
    (∀ {d n m : ℕ} (P : Fin n → E d) (Q : Fin m → E d) (R : Rect n m)
        (s₁ s₂ t₁ t₂ : ℝ × ℝ),
        s₁ ∈ R.inB → s₂ ∈ R.inB → t₁ ∈ R.outB → t₂ ∈ R.outB →
        R.inPos s₁ ≤ R.inPos s₂ → R.outPos t₁ ≤ R.outPos t₂ →
        ∀ (γ₁ : Path s₁ t₂) (γ₂ : Path s₂ t₁), BiMono γ₁ → BiMono γ₂ →
          (∀ u, γ₁ u ∈ R.carrier) → (∀ u, γ₂ u ∈ R.carrier) →
          (∃ u v, γ₁ u = γ₂ v) ∧
          ∀ c : ℝ, (∀ u, γ₁ u ∈ freeSpace P Q c) → (∀ u, γ₂ u ∈ freeSpace P Q c) →
            ∀ u v : unitInterval, γ₁ u = γ₂ v →
              (∃ π : Path s₁ t₁, BiMono π ∧
                Set.range π = γ₁ '' Set.Icc 0 u ∪ γ₂ '' Set.Icc v 1 ∧
                ∀ w, π w ∈ R.carrier ∩ freeSpace P Q c) ∧
              (∃ π : Path s₂ t₂, BiMono π ∧
                Set.range π = γ₂ '' Set.Icc 0 v ∪ γ₁ '' Set.Icc u 1 ∧
                ∀ w, π w ∈ R.carrier ∩ freeSpace P Q c)) ∧
    (∃ A : Program, Admissible A ∧ ∃ C : ℝ,
      ∀ {n m : ℕ} (R : Rect n m) (s₁ s₂ t₁ t₂ : ℝ × ℝ) (w₁ w₂ : List (ℝ × ℝ)),
        s₁ ∈ R.inB → s₂ ∈ R.inB → t₁ ∈ R.outB → t₂ ∈ R.outB →
        R.inPos s₁ ≤ R.inPos s₂ → R.outPos t₁ ≤ R.outPos t₂ →
        IsMonoPolyline w₁ s₁ t₂ → IsMonoPolyline w₂ s₂ t₁ →
        (∀ z ∈ w₁, z ∈ R.carrier) → (∀ z ∈ w₂, z ∈ R.carrier) →
        ∃ z : ℝ × ℝ,
          ComputesPointWithin A
            (initCfg [(w₁.length : ℤ), (w₂.length : ℤ)] (flatPts w₁ ++ flatPts w₂))
            (C * ((w₁.length : ℝ) + w₂.length)) z ∧
          z ∈ polyline w₁ ∧ z ∈ polyline w₂ ∧
          (IsGridPath w₁ → IsGridPath w₂ → ∃ i j : ℤ, z = ((i : ℝ), (j : ℝ)))) := by sorry

end FrechetNearLinear.Main
