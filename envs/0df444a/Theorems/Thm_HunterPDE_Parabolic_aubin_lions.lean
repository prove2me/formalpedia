-- Prove2me | Theorems.Thm_HunterPDE_Parabolic_aubin_lions
-- name    : HunterPDE.Parabolic.aubin_lions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:18:34.605333+00:00
-- url     : https://prove2.me/theorems/81255fbe-11ff-416a-add9-c478e13edade
-- title:
--   Theorem 6.9 — Aubin–Lions compactness in L²(0,T;Y)
-- statement:
--   Let $X \hookrightarrow Y \hookrightarrow Z$ be real Banach spaces (continuous injective linear embeddings $i : X \to Y$, $j : Y \to Z$), where $X$ and $Z$ are reflexive and $X$ is compactly embedded in $Y$. Let $1 < p < \infty$ and $T > 0$. If the functions $u_N : (0,T) \to X$ are such that $\{u_N\}$ is uniformly bounded in $L^2(0,T;X)$ and their weak time derivatives $\{u_{Nt}\}$, taken in $Z$, are uniformly bounded in $L^p(0,T;Z)$, then there is a subsequence $u_{N_k}$ and $w \in L^2(0,T;Y)$ with
--   $$\|u_{N_k} - w\|_{L^2(0,T;Y)} \to 0 \qquad (k \to \infty).$$
--
--   This is the compactness theorem used to pass to the limit in nonlinear terms of Galerkin approximations (§6.6).
--
--   **Formalization Note.** Reflexivity is surjectivity of the canonical map into the bidual (`NormedSpace.inclusionInDoubleDual`). The weak derivative is (6.14) with $u_N$ read in $Z$ through $j \circ i$. "Uniformly bounded" is one bound $M$ for all $N$, with $u_N \in L^2(0,T;X)$ and $u_{Nt} \in L^p(0,T;Z)$; norms are `eLpNorm` on $(0,T)$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 190, Theorem 6.9

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_WeakTimeDeriv

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HunterPDE.Parabolic

/-- Theorem 6.9 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 190 (Aubin–Lions
compactness): let `X ↪ Y ↪ Z` be Banach spaces (continuous injective linear embeddings
`i : X → Y`, `j : Y → Z`), with `X` and `Z` reflexive (the canonical map into the bidual is
onto) and `X` compactly embedded in `Y` (`i` compact). Let `1 < p < ∞` and `T > 0`. If the
functions `u_N : (0, T) → X` are uniformly bounded in `L²(0, T; X)` and their weak time
derivatives `u_{Nt}` (taken in `Z`, (6.14)) are uniformly bounded in `L^p(0, T; Z)`, then a
subsequence `u_{N_k}` converges strongly in `L²(0, T; Y)`: there is `w ∈ L²(0, T; Y)` with
`‖u_{N_k} − w‖_{L²(0,T;Y)} → 0`. -/
theorem aubin_lions {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (i : X →L[ℝ] Y) (j : Y →L[ℝ] Z) (hi : Function.Injective i) (hj : Function.Injective j)
    (hcpt : IsCompactOperator i)
    (hXrefl : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (hZrefl : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ Z))
    (p : ℝ≥0∞) (hp1 : 1 < p) (hpfin : p < ∞) (T : ℝ) (hT : 0 < T)
    (uN : ℕ → ℝ → X) (uNt : ℕ → ℝ → Z)
    (hderiv : ∀ N, HasWeakTimeDeriv (j.comp i) T (uN N) (uNt N))
    (hmem : ∀ N, MemLp (uN N) 2 (volume.restrict (Set.Ioo 0 T)))
    (hmemt : ∀ N, MemLp (uNt N) p (volume.restrict (Set.Ioo 0 T)))
    (M : ℝ≥0) (hbound : ∀ N, eLpNorm (uN N) 2 (volume.restrict (Set.Ioo 0 T)) ≤ M)
    (hboundt : ∀ N, eLpNorm (uNt N) p (volume.restrict (Set.Ioo 0 T)) ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℝ → Y, MemLp w 2 (volume.restrict (Set.Ioo 0 T)) ∧
      Tendsto (fun k => eLpNorm (fun t => i (uN (φ k) t) - w t) 2
        (volume.restrict (Set.Ioo 0 T))) atTop (𝓝 0) := by sorry

end HunterPDE.Parabolic
