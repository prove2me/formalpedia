-- Prove2me | Theorems.Thm_InterpOptStop_SAA_Supplement_lemma_EC_6
-- name    : InterpOptStop.SAA.Supplement.lemma_EC_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T22:50:00.285791+00:00
-- url     : https://prove2.me/theorems/cd53404c-b4c0-468e-9b46-65901da58433
-- title:
--   Lemma EC.6 — arbitrary-law estimate in one cube
-- statement:
--   Fix a positive subdivision count $m$, nonnegative $L$ and $\beta\in[0,1]$. Let $g$ and $c$ be Euclidean $L$-Lipschitz real functions on $[0,1]^n$. Let $z,z'$ have any probability laws supported in the same grid cell. No independence or equality of their laws is required. Then
--   $$E_z\left[\max\{g(z),\beta c(z)\}-\max\{E_{z'}g(z'),E_{z'}[\beta c(z')]\}\right]\le\frac{2L\sqrt n}{m}.$$
--   At a source period $t$, take $g=g(t,\cdot)$ and $c=C_t^*$. This is the local loss estimate for the averaged action on a cell. The two probability measures in Lean encode the two arbitrary laws directly.
--
--   Differences from the source:
--   - generalization: g(t,·) and the Bellman continuation C*_t at a fixed period t → any two Euclidean L-Lipschitz functions g and c on the cube; reason: the local estimate uses only their Lipschitz bounds and specializes by substituting the source functions
--   - reading: integer subdivision m and the unique cube h(x) → positive natural m, with shared faces owned by the lower cell and 0 included in the first cell; reason: m≤0 does not define a subdivision; unique face ownership completes the source partition and agrees with the published ≤-left splits
--   - encoding: random variables z and z′ in one hypercube → two probability laws almost surely supported in the same cell; reason: the expression depends only on the marginal laws, so this preserves all joint distributions and adds no independence requirement
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, Lemma EC.6, p. ec26

import Mathlib
import Definitions.Def_InterpOptStop_SAA_Supplement_GridPolicy

open MeasureTheory ProbabilityTheory

namespace InterpOptStop.SAA.Supplement

/-- The local estimate applies to arbitrary laws, without any coupling restriction. -/
theorem lemma_EC_6 {n : ℕ} (m : ℕ) (hm : 0 < m)
    (β L : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hL : 0 ≤ L)
    (g c : Cube n → ℝ) (hg : EuclideanLipschitz L g) (hc : EuclideanLipschitz L c)
    (ν ν' : Measure (Cube n)) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (h : Fin n → Fin m) (hz : ∀ᵐ z ∂ν, InCell h z) (hz' : ∀ᵐ z ∂ν', InCell h z) :
    (∫ z, (max (g z) (β * c z) -
      max (∫ z', g z' ∂ν') (∫ z', β * c z' ∂ν')) ∂ν) ≤
        2 * L * Real.sqrt n / m := by sorry

end InterpOptStop.SAA.Supplement
