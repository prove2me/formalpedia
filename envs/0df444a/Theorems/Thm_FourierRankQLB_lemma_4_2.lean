-- Prove2me | Theorems.Thm_FourierRankQLB_lemma_4_2
-- name    : FourierRankQLB.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:41.66406+00:00
-- url     : https://prove2.me/theorems/714907a4-5f8a-40b6-98a8-ca80e25c15be
-- title:
--   Lemma 4.2 — the membership phase has Fourier rank at most one
-- statement:
--   Let $d=d_n\ge2$, $q\in\mathbb R^d$ and $\tau\in\mathbb R$. The membership phase $\phi_{q,\tau}(Q)=(-1)^{\mathbf 1[q^TQq\le\tau]}$ lies in $V_1^{(d)}$. More precisely, there are trigonometric polynomials
--   $$
--   p_a(Q)=\sum_{j=-a}^ac_{a,j}e^{it_{a,j}q^TQq}=\sum_{j=-a}^ac_{a,j}\chi_{t_{a,j}qq^T}(Q)
--   $$
--   with $|p_a(Q)|\le1$ such that $p_a\to\phi_{q,\tau}$ almost everywhere and in $L^2(O(d),\mu_d)$.
--
--   A discontinuous Boolean answer therefore costs only one unit of Fourier rank.
--
--   Differences from the source:
--
--   - encoding: $d=d_n$ of §4.2 → hypotheses `2 ≤ d`, `Even d`; reason: these are exactly the values of $d_n$ for $n\ge2$
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Lemma 4.2, p.26

import Mathlib
import Definitions.Def_FourierRankQLB_phase
import Definitions.Def_FourierRankQLB_Vr

open MeasureTheory Filter Matrix
open scoped Topology

namespace FourierRankQLB

/-- Lemma 4.2 (The membership phase has Fourier rank at most one). `ϕ_{q,τ} ∈ V_1^{(d)}`. More precisely
there are trigonometric polynomials `p_a(Q) = ∑_{j=-a}^{a} c_{a,j} e^{i t_{a,j} qᵀQq}
= ∑_{j=-a}^{a} c_{a,j} χ_{t_{a,j} qqᵀ}(Q)` (42) with `|p_a| ≤ 1`, and `p_a → ϕ_{q,τ}` almost
everywhere and in `L²(O(d), μ_d)`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Lemma 4.2, p. 26.

**Formalization Note.** `d` is even and at least `2`: it is `d_n` for `n ≥ 2`. The `L²` convergence is
stated as `‖p_a - ϕ_{q,τ}‖₂ → 0`. -/
theorem lemma_4_2 {d : ℕ} (hd : 2 ≤ d) (hev : Even d) (q : Fin d → ℝ) (τ : ℝ) :
    (∃ f ∈ Vr d 1, f =ᵐ[haarO d] phase q τ) ∧
    ∃ (c : ℕ → ℤ → ℂ) (t : ℕ → ℤ → ℝ) (p : ℕ → Od d → ℂ),
      (∀ a Q, p a Q = ∑ j ∈ Finset.Icc (-(a : ℤ)) a, c a j * Complex.exp (Complex.I * (t a j : ℂ) *
        ((q ⬝ᵥ ((Q : Matrix (Fin d) (Fin d) ℝ) *ᵥ q) : ℝ) : ℂ))) ∧
      (∀ a Q, p a Q = ∑ j ∈ Finset.Icc (-(a : ℤ)) a, c a j * chi (t a j • vecMulVec q q) Q) ∧
      (∀ a Q, ‖p a Q‖ ≤ 1) ∧
      (∀ᵐ Q ∂haarO d, Tendsto (fun a => p a Q) atTop (𝓝 (phase q τ Q))) ∧
      Tendsto (fun a => eLpNorm (fun Q => p a Q - phase q τ Q) 2 (haarO d)) atTop (𝓝 0) := by sorry

end FourierRankQLB
