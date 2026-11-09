-- Prove2me | Theorems.Thm_GevreyGibbsSep_lemma_A_9
-- name    : GevreyGibbsSep.lemma_A_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:35:53.255441+00:00
-- url     : https://prove2.me/theorems/27609609-0183-469c-9527-3c1dc44002e7
-- title:
--   Lemma A.9 — annealing succeeds with probability $\ge(e^{-1/8}-\varepsilon/32)^2>1/2$
-- statement:
--   Let $\beta>0$, $0<\varepsilon<1/2$ and $\Delta=\max E-\min E$ with $e^{\beta\Delta}\le\alpha$. On one common grid use $n=\max\{1,\lceil(\log\alpha)^2/4\rceil\}$ steps, $\beta_k=k\beta/n$, with $\psi_k$ the grid Gibbs state at $\beta_k$ ($\psi_0$ uniform), and let $F_k$ ($k=1,\dots,n$) be the successful branches of the filters: contractions with
--   $$\|F_k-|\psi_k\rangle\langle\psi_k|\|\le2\tilde\varepsilon,\qquad\tilde\varepsilon=\frac{\varepsilon}{64n}.$$
--   With $y_k=F_k\cdots F_1\psi_0$:
--
--   1. one complete attempt succeeds with probability $\|y_n\|^2\ge(e^{-1/8}-\varepsilon/32)^2>1/2$;
--   2. conditional on success, the normalized final state satisfies $\|y_n/\|y_n\|-\psi_n\|<\varepsilon/8$;
--   3. every successful prefix $y_k$, $k<n$, is nonzero and a constant-overlap warm start for the next filter: $|\langle\psi_{k+1},y_k/\|y_k\|\rangle|>1/2$.
--
--   **Formalization Note** The source assumes ground-state vector errors and filter operator errors at most $\tilde\varepsilon$; its proof derives and uses only $\|F_k-\Pi_k\|\le2\tilde\varepsilon$ for contractions $F_k$, which is the hypothesis here. The constant of the warm start is the $1/2$ of the proof.
--
--   Differences from the source:
--   - generalization: ground-state vector error and filter operator error at most $\tilde\varepsilon$ at each step → contractions $F_k$ with $\|F_k-|\psi_k\rangle\langle\psi_k|\|\le2\tilde\varepsilon$; reason: the source's hypotheses imply this ($\||g\rangle\langle g|-|\psi\rangle\langle\psi|\|\le\|g-\psi\|$ for unit vectors), and the proof uses only it
--   - generalization: one common grid → any finite nonempty set $G$ and $E:G\to\mathbb R$; reason: the grid is one finite set
--   - reading: "every successful prefix is a constant-overlap warm start for the next filter" → $y_k\ne0$ and $|\langle\psi_{k+1},y_k/\|y_k\|\rangle|>1/2$ for every $k<n$; reason: the proof establishes overlap $>1/2$ with the next ground state
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Lemma A.9, Eq. (A83), p.32; proof pp.32

import Mathlib
import Definitions.Def_GevreyGibbsSep_finiteGibbsState

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Lemma A.9 (success probability of the annealed Gibbs sampler), arXiv:2608.24527 (sha256
d4fd40eb…), Eq. (A83), p.32. Let `β > 0`, `0 < ε < 1/2`, `e^{β∆} ≤ α`,
`n = max{1, ⌈(log α)²/4⌉}`, `β_k = kβ/n`, `ψ_k` the grid Gibbs state at `β_k`, `ε̃ = ε/(64n)`, and
let the successful filter branches `F_k` (`k = 1, …, n`) be contractions with
`‖F_k − |ψ_k⟩⟨ψ_k|‖ ≤ 2ε̃`. With `y_k = F_k ⋯ F_1 ψ_0`: the success probability satisfies
`‖y_n‖² ≥ (e^{−1/8} − ε/32)² > 1/2`, the normalized final state is within `ε/8` of `ψ_n`, and
every prefix `y_k`, `k < n`, is nonzero with overlap `> 1/2` with the next state `ψ_{k+1}`
(a constant-overlap warm start).

**Formalization Note** The source's hypotheses "ground-state vector error and filter operator
error at most `ε̃`" are replaced by their consequence `‖F_k − Π_k‖ ≤ 2ε̃`, which the proof states
and uses (p.32). The grid is any finite nonempty set `G`. -/
theorem lemma_A_9 {G : Type*} [Fintype G] [Nonempty G] (E : G → ℝ) (β ε α : ℝ)
    (hβ : 0 < β) (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (hα : Real.exp (β * (Finset.univ.sup' Finset.univ_nonempty E
        - Finset.univ.inf' Finset.univ_nonempty E)) ≤ α)
    (n : ℕ) (hn : n = max 1 ⌈Real.log α ^ 2 / 4⌉₊)
    (F : ℕ → (EuclideanSpace ℂ G →L[ℂ] EuclideanSpace ℂ G))
    (hF : ∀ k, 1 ≤ k → k ≤ n →
      ‖F k‖ ≤ 1 ∧
      ‖F k - (innerSL ℂ (finiteGibbsState E (k * β / n))).smulRight
          (finiteGibbsState E (k * β / n))‖ ≤ 2 * (ε / (64 * n))) :
    let ψ : ℕ → EuclideanSpace ℂ G := fun k => finiteGibbsState E (k * β / n)
    let y : ℕ → EuclideanSpace ℂ G := fun k => Nat.rec (ψ 0) (fun j yj => F (j + 1) yj) k
    (Real.exp (-1 / 8) - ε / 32) ^ 2 ≤ ‖y n‖ ^ 2 ∧ 1 / 2 < (Real.exp (-1 / 8) - ε / 32) ^ 2 ∧
    ‖((‖y n‖⁻¹ : ℝ) : ℂ) • y n - ψ n‖ < ε / 8 ∧
    ∀ k < n, y k ≠ 0 ∧ 1 / 2 < ‖⟪ψ (k + 1), ((‖y k‖⁻¹ : ℝ) : ℂ) • y k⟫_ℂ‖ := by sorry

end GevreyGibbsSep
