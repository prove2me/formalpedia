-- Prove2me | Theorems.Thm_MatrixSpencer_lemma_2_4
-- name    : MatrixSpencer.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:42:18.715452+00:00
-- url     : https://prove2.me/theorems/1464f8bc-7d28-4e1b-a8c0-ee61db791c05
-- title:
--   Lemma 2.4, p.8 — Gaussian trace moments
-- statement:
--   Let $M_1,\dots,M_n\in\mathbb R^{d\times d}$ be symmetric with $V:=\sum_iM_i^2\preceq\eta I_d$ for some $\eta\ge0$, and $X(g)=\sum_ig_iM_i$. Then for every integer $k\ge1$,
--
--   $$\mathbb E_{\gamma_n}\mathrm{Tr}\,X^{2k}\le d(2k-1)!!\,\eta^k\le d(2k\eta)^k.$$
--
--   These bounds control the moments of $B_t$ and $Y$ along the interpolation.
--
--   Differences from the source:
--   - encoding: E Tr X^{2k} implicitly well defined → integrability of Tr X^{2k} is in the conclusion; reason: Lean's integral of a non-integrable function is 0; the trace is a polynomial in g
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma 2.4, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_MatrixSpencer_gam
import Definitions.Def_MatrixSpencer_series
open scoped Nat

namespace MatrixSpencer

/-- **Lemma 2.4 (Gaussian trace moments).**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma 2.4, p.8 (PDF p.10): "Let M₁, …, Mₙ ∈ ℝ^{d×d} be symmetric matrices satisfying
V := ∑ⁿᵢ₌₁ Mᵢ² ⪯ ηI_d, for some η ≥ 0, and denote X(g) = ∑ⁿᵢ₌₁ gᵢMᵢ. Then, for every integer k ≥ 1,
E_{γₙ} Tr X^{2k} ≤ d(2k − 1)!! η^k ≤ d(2kη)^k."

**Formalization Note.** The conclusion also states that `Tr X^{2k}` is integrable, so the Bochner
integral is not a junk `0`. -/
theorem lemma_2_4 {n d : ℕ} (M : Fin n → Matrix (Fin d) (Fin d) ℝ) (hM : ∀ i, (M i).IsSymm)
    (η : ℝ) (hη : 0 ≤ η)
    (hV : (η • (1 : Matrix (Fin d) (Fin d) ℝ) - ∑ i, M i ^ 2).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) :
    MeasureTheory.Integrable (fun g => ((series M g) ^ (2 * k)).trace) (gam n) ∧
      ∫ g, ((series M g) ^ (2 * k)).trace ∂(gam n) ≤ d * ((2 * k - 1)‼ : ℕ) * η ^ k ∧
      (d : ℝ) * ((2 * k - 1)‼ : ℕ) * η ^ k ≤ d * (2 * k * η) ^ k := by sorry

end MatrixSpencer
