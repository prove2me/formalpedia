-- Prove2me | Theorems.Thm_LocalParametrix_continuous_fourier_and_contDiffOn_compl_zero_of_norm_iteratedFDeriv_le
-- name    : LocalParametrix.continuous_fourier_and_contDiffOn_compl_zero_of_norm_iteratedFDeriv_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/c3664ebd-b633-5925-b0d5-4db97dd846f8
-- title:
--   Fourier transform of a decaying symbol: continuity and smoothness off 0
-- statement:
--   Let $V$ be a finite-dimensional real inner product space, equipped with its Borel $\sigma$-algebra and the associated volume measure, and let $r \colon V \to \mathbb{C}$ be infinitely differentiable (of class $C^\infty$ in the Fréchet sense over $\mathbb{R}$). Let $s$ be a real number with $s > \dim_{\mathbb{R}} V$, and suppose that for every natural number $n$ there is a real constant $C$ such that the $n$-th iterated Fréchet derivative satisfies the symbol estimate $\|D^n r(\xi)\| \le C\,(1+\|\xi\|)^{-(s+n)}$ for all $\xi \in V$, the exponent being a real power. The conclusion is twofold: the Fourier transform $\widehat{r}(x) = \int_V e^{-2\pi i \langle \xi, x\rangle} r(\xi)\, d\xi$, taken with respect to the volume measure and the inner product pairing of $V$, is continuous on all of $V$; and its restriction to the complement of $\{0\}$ is of class $C^\infty$ there, i.e. $\widehat{r}$ is infinitely differentiable on $V \setminus \{0\}$ in the sense of `ContDiffOn`.
--
--   This is the function-level form of the classical statement that the kernel of a Fourier multiplier whose symbol has order strictly less than $-\dim V$ is continuous and smooth away from the diagonal. It is used in the construction of a local parametrix, where the global kernel of an elliptic operator must be cut off near its pole, and is cited by [`LocalParametrix.exists_continuous_contDiffOn_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top`](thm.html#LocalParametrix.exists_continuous_contDiffOn_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalParametrix_continuous_fourier_and_contDiffOn_compl_zero_of_norm_iteratedFDeriv_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory FourierTransform

theorem LocalParametrix.continuous_fourier_and_contDiffOn_compl_zero_of_norm_iteratedFDeriv_le
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (r : V → ℂ) (hr : ContDiff ℝ (⊤ : ℕ∞) r) (s : ℝ) (hs : (Module.finrank ℝ V : ℝ) < s)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ ξ : V, ‖iteratedFDeriv ℝ n r ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-(s + n))) :
    Continuous (𝓕 r) ∧ ContDiffOn ℝ (⊤ : ℕ∞) (𝓕 r) {0}ᶜ := by sorry
