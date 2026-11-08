-- Prove2me | Theorems.Thm_HardcoreSlices_lemma_4_1
-- name    : HardcoreSlices.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:38:36.117436+00:00
-- url     : https://prove2.me/theorems/2789306c-6456-40a0-b3da-f24352fdf951
-- title:
--   Lemma 4.1 — top-link expansion of the two-sided slice (corrected: positive denominator)
-- statement:
--   Let $G=(X,Y,E)$ be a $\Delta$-regular bipartite graph with $|X|=|Y|=m\ge2$, let $k_X,k_Y\le m$, and let $\tau=(\tau_X,\tau_Y)$ be a face of the two-sided slice $(\mathcal X,\mu^{(k_X,k_Y)})$.
--
--   1. If $\tau\in\mathcal I_{k_X-1,k_Y-1}(G)$ and the minimum below is positive, then
--   $$\lambda_2(P_\tau)\le\frac{\lambda_2(A_G)}{\min\{|X\setminus(\tau_X\cup N(\tau_Y))|-\Delta,\ |Y\setminus(\tau_Y\cup N(\tau_X))|-\Delta\}}.$$
--   2. If $\tau\in\mathcal I_{k_X-2,k_Y}(G)$ or $\tau\in\mathcal I_{k_X,k_Y-2}(G)$, then $\lambda_2(P_\tau)\le0$.
--
--   This deterministic bound and Friedman's theorem give the top-link expansion of Theorem 1.8.
--
--   Differences from the source:
--   - correction: for large enough |X| → m ≥ 2 and 0 < min{…} in clause 1; reason: k is free, so large |X| does not exclude min ≤ 0: m = 10, ∆ = 2, G = C₂₀ with x_i ~ y_i, y_{i−1}, τX = ∅, τY = {y1, y3, y5, y7, y8}, kX = 1, kY = 6 has min = −1, bound ≈ −1.90 and λ2(Pτ) = 0
--   - encoding: λ2(Pτ) ≤ b → HDXConc.SecondEigLE in Rayleigh form; reason: equivalent by Courant–Fischer for a reversible walk on at least two vertices, with no eigenvalue sort
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Lemma 4.1, p.19

import Mathlib
import Definitions.Def_HardcoreSlices_twoSidedSlice
import Definitions.Def_HardcoreSlices_lam2
import Definitions.Def_HDXConc_linkWeight
import Definitions.Def_HDXConc_SecondEigLE

open Classical

namespace HardcoreSlices

open ExpanderBIS.RandomHardCore

/-- **Lemma 4.1 (corrected: positive denominator).** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), p.19: "Fix `kX, kY ≤ |X|` and let `(X, µ(kX,kY))` be the two-sided independent set slice of a
`∆`-regular bipartite graph `G = (X, Y, E)`. Let `τ = (τX, τY) ∈ X` satisfy `codim(τ) = 2`. We show for large enough `|X|` the complex satisfies:
1. For `τ ∈ IkX−1,kY−1(G)`, `λ2(Pτ) ≤ λ2(AG) / min{ |X \ (τX ∪ N(τY))| − ∆, |Y \ (τY ∪ N(τX))| − ∆ }`.
2. For `τ ∈ IkX−2,kY(G)` or `IkX,kY−2(G)`, `λ2(Pτ) ≤ 0`."

**Formalization Note.** The statement is deterministic in `G`. Clause 1 adds `0 < min{…}`, since "large enough `|X|`" does not exclude `min ≤ 0`, as `kX, kY` are free.
Counterexample: `m = 10`, `∆ = 2`, `G = C₂₀` with `x_i ~ y_i, y_{i−1}`, `τX = ∅`, `τY = {y1, y3, y5, y7, y8}`, so `kX = 1`, `kY = 6`; then
`min = −1`, the bound is about `−1.90`, while the link is a star with `λ2(Pτ) = 0`. "Large enough `|X|`" is otherwise `m ≥ 2`.
`λ2(Pτ) ≤ b` is the Rayleigh form `HDXConc.SecondEigLE`. -/
theorem lemma_4_1 {m Δ : ℕ} (G : SimpleGraph (Vertex m)) (hG : IsBipReg G Δ) (hm : 2 ≤ m) (kX kY : ℕ)
    (hkX : kX ≤ m) (hkY : kY ≤ m) (τ : Finset (Vertex m)) (hτ : τ ∈ twoSidedComplex G kX kY) :
    ((τ ∩ oddSide m).card + 1 = kX → (τ ∩ evenSide m).card + 1 = kY →
      0 < min (((freeSide G false τ).card : ℝ) - Δ) (((freeSide G true τ).card : ℝ) - Δ) →
      HDXConc.SecondEigLE (HDXConc.linkVerts (twoSidedComplex G kX kY) τ)
        (HDXConc.linkWeight (twoSidedComplex G kX kY) (kX + kY) (twoSidedLaw G kX kY) τ)
        (lam2 G / min (((freeSide G false τ).card : ℝ) - Δ) (((freeSide G true τ).card : ℝ) - Δ))) ∧
    (((τ ∩ oddSide m).card + 2 = kX ∧ (τ ∩ evenSide m).card = kY) ∨
        ((τ ∩ oddSide m).card = kX ∧ (τ ∩ evenSide m).card + 2 = kY) →
      HDXConc.SecondEigLE (HDXConc.linkVerts (twoSidedComplex G kX kY) τ)
        (HDXConc.linkWeight (twoSidedComplex G kX kY) (kX + kY) (twoSidedLaw G kX kY) τ) 0) := by sorry

end HardcoreSlices
