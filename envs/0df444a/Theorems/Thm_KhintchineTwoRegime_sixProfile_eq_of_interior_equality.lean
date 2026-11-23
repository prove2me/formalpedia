-- Prove2me | Theorems.Thm_KhintchineTwoRegime_sixProfile_eq_of_interior_equality
-- name    : KhintchineTwoRegime.sixProfile_eq_of_interior_equality
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:41:45.249863+00:00
-- url     : https://prove2.me/theorems/e9f605ed-807e-4192-9235-74ee34d14e7a
-- title:
--   Equality characterization in the interior six-coordinate regime
-- statement:
--   Let $n\ge6$ and $d_0<\tau\le d_1$, and put $q=(2-\tau^2)/\sqrt2$. Suppose $\omega\in\mathcal C_n(\tau)$ satisfies $K_n(\omega)=A(q)$ and
--   $$
--   x=q-\omega_3-\omega_4=0.
--   $$
--   Then $\omega=\omega^{(6)}_\tau$.
--
--   In the equality case of the proof of Theorem 2, the first four coefficients are all $q/2$. Equality in the tail Khintchine inequality leaves exactly two equal nonzero tail coefficients; properness and unit normalization identify them with the final two coefficients of $\omega^{(6)}_\tau$.
--
--   **Formalization Note** Coordinates are zero-based and read using `pad`, so the hypothesis on $x$ is $\omega_1+\omega_2-\omega_3-\omega_4=0$.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2, proof of Theorem 2, p.8 (the equality case following 'with equality only if x = 0').

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_KhintchineTwoRegime_Cn
import Definitions.Def_KhintchineTwoRegime_sixProfile
import Definitions.Def_KhintchineTwoRegime_Abound
import Definitions.Def_KhintchineTwoRegime_pad

theorem KhintchineTwoRegime.sixProfile_eq_of_interior_equality (n : ℕ) (hn : 6 ≤ n) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (Real.sqrt (2 - Real.sqrt 2)) (Real.sqrt (2 - Real.sqrt 966 / 22)))
    (hτ₀ : Real.sqrt (2 - Real.sqrt 2) < τ) (ω : Fin n → ℝ) (hω : ω ∈ Cn n τ)
    (hK : K n ω = Abound ((2 - τ ^ 2) / Real.sqrt 2))
    (hx : pad ω 0 + pad ω 1 - pad ω 2 - pad ω 3 = 0) :
    ω = sixProfile n τ := by sorry
