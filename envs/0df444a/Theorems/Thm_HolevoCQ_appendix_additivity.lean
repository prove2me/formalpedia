-- Prove2me | Theorems.Thm_HolevoCQ_appendix_additivity
-- name    : HolevoCQ.appendix_additivity
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:59.282075+00:00
-- url     : https://prove2.me/theorems/4517442c-69f7-4821-b827-2c3caedbf1b0
-- title:
--   Appendix: $\max\Delta H$ is additive for product channels
-- statement:
--   Let $A_1,A_2$ be finite alphabets and let $\{S^1_i,\ i\in A_1\}$ and $\{S^2_j,\ j\in A_2\}$ be families of density operators on finite-dimensional Hilbert spaces $\mathcal H_1$, $\mathcal H_2$. For a distribution $\{\pi_{ij}\}$ on $A_1\times A_2$ let
--
--   $$
--   \Delta H(\{\pi_{ij}\})=H\Big(\sum_{ij}\pi_{ij}S^1_i\otimes S^2_j\Big)-\sum_{ij}\pi_{ij}H(S^1_i\otimes S^2_j).
--   $$
--
--   Then
--
--   $$
--   \max_{\pi_{ij}}\Delta H(\{\pi_{ij}\})=\max_{\pi^1}\Delta H(\{\pi^1_i\})+\max_{\pi^2}\Delta H(\{\pi^2_j\}).
--   $$
--
--   Iterated, this shows that the entropy bound of the $n$-fold product channel is $n$ times that of the channel, which turns the one-shot entropy bound into the upper bound $C\le\max_\pi\Delta H(\pi)$.
--
--   Differences from the source:
--   - encoding: finite alphabets $A_1,A_2$; Hilbert spaces $\mathcal H_1,\mathcal H_2$; $\mathcal H_1\otimes\mathcal H_2$ → finite types `A₁`, `A₂` with `[Nonempty _]`; $\mathbb C^{D_1}$, $\mathbb C^{D_2}$; Kronecker product on `D₁ × D₂`; reason: Lean convention; an empty alphabet carries no distribution, so the maxima would be undefined
--   - reading: Hilbert spaces $\mathcal H_k$ of unstated dimension → finite-dimensional $\mathcal H_k=\mathbb C^{D_k}$; reason: the paper's standing assumption (p.1) is a finite-dimensional $\mathcal H$; in infinite dimension $H$ can be $+\infty$ and the identity has another meaning
--   - encoding: $\max$ over distributions → real supremum `⨆` over the probability simplex; reason: each set is nonempty and bounded above by $\log_2$ of the dimension and the maximum is attained (continuous function on a compact simplex), so the supremum is the maximum
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, Appendix, p.7

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_HolevoCQ_holevoChi

open QAlgorithms
open scoped Kronecker

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, Appendix, p.7: for finite alphabets `A₁, A₂` and families of density
operators `{S¹_i, i ∈ A₁}` in `H₁`, `{S²_j, j ∈ A₂}` in `H₂`, with
`ΔH({π_ij}) = H(Σ_ij π_ij S¹_i ⊗ S²_j) − Σ_ij π_ij H(S¹_i ⊗ S²_j)` for distributions on `A₁ × A₂`,
`max_{π_ij} ΔH({π_ij}) = max_{π¹} ΔH({π¹_i}) + max_{π²} ΔH({π²_j})`.

**Formalization Note.** `H₁ = ℂ^{D₁}`, `H₂ = ℂ^{D₂}` are finite-dimensional (the paper's standing
assumption, p.1) and `H₁ ⊗ H₂ = ℂ^{D₁ × D₂}` with the Kronecker product. The maxima are written
as real suprema over the probability simplices; each is over a nonempty set (`[Nonempty A_k]`)
and bounded above, so it is the paper's maximum whenever that maximum exists. -/
theorem appendix_additivity {A₁ A₂ D₁ D₂ : Type} [Fintype A₁] [DecidableEq A₁] [Nonempty A₁]
    [Fintype A₂] [DecidableEq A₂] [Nonempty A₂] [Fintype D₁] [DecidableEq D₁] [Fintype D₂]
    [DecidableEq D₂] (S₁ : A₁ → Matrix D₁ D₁ ℂ) (S₂ : A₂ → Matrix D₂ D₂ ℂ)
    (hS₁ : ∀ i, IsDensityMatrix (S₁ i)) (hS₂ : ∀ j, IsDensityMatrix (S₂ j)) :
    (⨆ π : stdSimplex ℝ (A₁ × A₂), holevoChi (fun ij : A₁ × A₂ => S₁ ij.1 ⊗ₖ S₂ ij.2) π) =
      (⨆ π : stdSimplex ℝ A₁, holevoChi S₁ π) + (⨆ π : stdSimplex ℝ A₂, holevoChi S₂ π) := by sorry

end HolevoCQ
