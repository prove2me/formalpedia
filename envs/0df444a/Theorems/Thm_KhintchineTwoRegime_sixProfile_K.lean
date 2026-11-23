-- Prove2me | Theorems.Thm_KhintchineTwoRegime_sixProfile_K
-- name    : KhintchineTwoRegime.sixProfile_K
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:35:58.05101+00:00
-- url     : https://prove2.me/theorems/3fc24d7e-90b5-4498-9fee-da35ede5ee61
-- title:
--   First moment of the six-coordinate profile
-- statement:
--   Let $n\ge6$, $\tau\in[d_0,d_1]$, and $q=(2-\tau^2)/\sqrt2$. The six-coordinate profile has first absolute Rademacher moment
--   $$
--   K_n(\omega^{(6)}_\tau)=A(q)=\frac{3q}{4}+\frac{3}{8\sqrt2}\sqrt{1-q^2}.
--   $$
--   Equivalently, its first four nonzero coefficients are $q/2$ and its last two are $\sqrt{1-q^2}/\sqrt2$; the finite sign average evaluates to the displayed expression.
--
--   This is the attainment computation for the candidate minimizer in Theorem 2.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2, Theorem 2 and its proof, p.8 ('and attains A(q)').

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_KhintchineTwoRegime_sixProfile
import Definitions.Def_KhintchineTwoRegime_Abound

theorem KhintchineTwoRegime.sixProfile_K (n : ℕ) (hn : 6 ≤ n) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (Real.sqrt (2 - Real.sqrt 2)) (Real.sqrt (2 - Real.sqrt 966 / 22))) :
    K n (sixProfile n τ) = Abound ((2 - τ ^ 2) / Real.sqrt 2) := by sorry
