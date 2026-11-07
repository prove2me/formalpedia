-- Prove2me | Theorems.Thm_MatrixSpencer_theorem_1_4
-- name    : MatrixSpencer.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:42:11.813451+00:00
-- url     : https://prove2.me/theorems/24d8593f-6fbd-4b81-a405-fc41f0e03cf6
-- title:
--   Theorem 1.4, p.2 — hereditary matrix small ball
-- statement:
--   Let $A_1,\dots,A_n\in\mathbb R^{d\times d}$ be symmetric matrices and set $\sigma^2=\|\sum_iA_i^2\|$. Then for every real $0<s\le d$, with $g\sim\mathcal N(0,I_n)$,
--
--   $$\mathbb P\Bigl\{\Bigl\|\sum_{i=1}^n g_iA_i\Bigr\|\le32\sigma\sqrt{1+\log(2d/s)}\Bigr\}\ge e^{-s/4}.$$
--
--   This is the Gaussian measure lower bound for the discrepancy body that makes the partial coloring method succeed, with $s=\min\{d,n\}$.
--
--   Differences from the source: none.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 1.4, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_MatrixSpencer_gam
import Definitions.Def_MatrixSpencer_series
open scoped Matrix.Norms.L2Operator

namespace MatrixSpencer

/-- **Theorem 1.4 (Hereditary matrix small ball).**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 1.4, p.2 (PDF p.4): "Let A₁, …, Aₙ ∈ ℝ^{d×d} be symmetric d × d matrices and set
σ² = ‖∑ⁿᵢ₌₁ Aᵢ²‖. Then, for every 0 < s ≤ d, ℙ{‖∑ⁿᵢ₌₁ gᵢAᵢ‖ ≤ 32σ√(1 + log(2d/s))} ≥ e^{−s/4}, where
g ∼ 𝒩(0, Iₙ)."

**Formalization Note.** `s` is real. The event is closed, so the probability is that of a measurable
set. `σ = √‖∑ᵢAᵢ²‖` may be `0`; then all `Aᵢ` vanish and the probability is `1`. -/
theorem theorem_1_4 {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ i, (A i).IsSymm)
    (s : ℝ) (hs0 : 0 < s) (hsd : s ≤ d) :
    Real.exp (-s / 4) ≤
      (gam n).real {g | ‖series A g‖ ≤ 32 * √‖∑ i, A i ^ 2‖ *
        √(1 + Real.log (2 * (d : ℝ) / s))} := by sorry

end MatrixSpencer
