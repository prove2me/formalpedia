-- Prove2me | Theorems.Thm_OCEClocks_DisplayAds_lemma_6
-- name    : OCEClocks.DisplayAds.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:22:09.236065+00:00
-- url     : https://prove2.me/theorems/03740abd-86db-4821-8c52-102973891e50
-- title:
--   Lemma 6 — fresh competing clocks: submodular expectations can only drop, supermodular ones only rise
-- statement:
--   Let $G$ be any OCEC generator, and let $x\in[0,1]^{I\times J}$ be fractional allocations with $\sum_{i}x_{ij}\le1$ for every request $j$, fixed independently of the randomness. Run OCEC rounding: independent copies $G_i$ return clocks $Y_{ij}$, discard clocks are $\bar Y_j\sim\mathrm{Exp}(1-\sum_ix_{ij})$, and $S_i$ is the set of requests allocated to $i$. Fix a resource $i$ and let
--
--   $$S_i^{\mathrm{Ind}}=\{j\in J:\ Y_{ij}<Z_j\},$$
--
--   where the fresh competing clocks $Z_j\sim\mathrm{Exp}(1-x_{ij})$ are independent of each other and of $i$'s generator. Then for every submodular $f:2^J\to\mathbb R$,
--
--   $$\mathbb E\big[f(S_i)\big]\ \ge\ \mathbb E\big[f(S_i^{\mathrm{Ind}})\big],$$
--
--   and the inequality reverses for every supermodular $f$.
--
--   This localises the analysis of each resource to its own generator. With $f(S)=\mathbf 1\{S\cap J_i(w)\neq\emptyset\}$ it gives Lemma 15.
--
--   **Formalization Note** Resources are `Fin m` and requests `Fin n`. $E[f(S_i)]$ is taken over `roundingLaw P x` and $E[f(S_i^{\mathrm{Ind}})]$ over `freshLaw P x i`, the product of $i$'s generator randomness with the fresh clocks. Since $S_i^{\mathrm{Ind}}$ depends only on $(Y_{ij})_j$ and $(Z_j)_j$, this is its law in any joint construction in which the $Z_j$ are independent of everything. Submodularity and supermodularity are the lattice inequalities of the platform definition `SteinitzExchange.Duality.IsSubmodular` / `IsSupermodular`.
--
--   Differences from the source:
--   - encoding: finite sets I (resources) and J (requests), J indexed in arrival order → Fin m and Fin n, with the order of Fin n as the arrival order; reason: every finite ordered set is in bijection with some Fin
--   - encoding: the resource with the minimum clock wins (ties have probability zero) → ties in the minimum go to the smallest index; reason: a null event; a deterministic rule is needed to define S_i on every outcome
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), p. 7, Lemma 6

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_SetFunction
import Definitions.Def_OCEClocks_DisplayAds_OCEC

open MeasureTheory
open scoped ENNReal

namespace OCEClocks.DisplayAds

/-- Lemma 6 (p. 7): for any OCEC generator, any allocation `x ∈ [0, 1]^{m × n}` with
`Σ_i x_ij ≤ 1`, and any resource `i`, replacing `i`'s competitors by fresh clocks
`Z_j ∼ Exp(1 - x_ij)` cannot increase `E[f(S_i)]` for submodular `f` and cannot decrease it for
supermodular `f`. -/
theorem lemma_6 (m n : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : (Fin n → ℝ) → Ω → Fin n → ℝ≥0∞) (hY : IsOCECGenerator P Y)
    (x : Fin m → Fin n → ℝ) (hx : ∀ i j, x i j ∈ Set.Icc (0 : ℝ) 1)
    (hsum : ∀ j, ∑ i, x i j ≤ 1) (i : Fin m) :
    (∀ f : Finset (Fin n) → ℝ, SteinitzExchange.Duality.IsSubmodular f →
      ∫ ω, f (freshAllocated Y x i ω) ∂freshLaw P x i ≤
        ∫ ω, f (allocated Y x ω i) ∂roundingLaw P x) ∧
    (∀ f : Finset (Fin n) → ℝ, SteinitzExchange.Duality.IsSupermodular f →
      ∫ ω, f (allocated Y x ω i) ∂roundingLaw P x ≤
        ∫ ω, f (freshAllocated Y x i ω) ∂freshLaw P x i) := by sorry

end OCEClocks.DisplayAds
