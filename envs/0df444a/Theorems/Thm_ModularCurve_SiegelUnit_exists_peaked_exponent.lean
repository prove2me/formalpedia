-- Prove2me | Theorems.Thm_ModularCurve_SiegelUnit_exists_peaked_exponent
-- name    : ModularCurve.SiegelUnit.exists_peaked_exponent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/e5836f26-551c-5a7a-9a9a-ed4e10f7c424
-- title:
--   Existence of a peaked Siegel-unit exponent vector at level N
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ and $2 \le N$. For an integer $t$ put $\widetilde{B}_N(t) = 6t^2 - 6Nt + N^2$, and for $u \in \mathbb{Z}/N$ let $\mathrm{rep}(u) \in \{0,\dots,N-1\}$ denote its least non-negative representative. The theorem asserts the existence of a function $m : \mathbb{Z}/N \times \mathbb{Z}/N \to \mathbb{N}$ and a function $\mathrm{Ord} : \mathbb{Z}/N \times \mathbb{Z}/N \to \mathbb{Z}$ such that: (i) for all $x,y \in \mathbb{Z}/N$ one has $\mathrm{Ord}(x,y) = \sum_{r}\sum_{s} m(r,s)\,\widetilde{B}_N\bigl(\mathrm{rep}(rx+sy)\bigr)$, both sums running over $\mathbb{Z}/N$ and $m(r,s)$ being regarded as an integer; (ii) $m(0,0) = 0$; (iii) $m(r, s+r) = m(r,s)$ for all $r,s \in \mathbb{Z}/N$; (iv) $0 < \mathrm{Ord}(1,0)$; and (v) for every pair $(x,y)$ for which there exist $a,b \in \mathbb{Z}/N$ with $ax+by = 1$, and such that it is not the case that $y = 0$ and $x \in \{1,-1\}$, and such that $y \neq 1$ and $y \neq -1$, one has the strict inequality $\mathrm{Ord}(1,0) < \mathrm{Ord}(x,y)$.
--
--   The weight $\widetilde{B}_N(t) = 6N^2\overline{B}_2(t/N)$ is the periodic second Bernoulli function, and $\mathrm{Ord}$ records (up to a normalising factor) the vanishing order at the cusp of $\Gamma(N)$ indexed by the primitive pair $(x,y)$ of a product of Siegel functions with exponents $m$, in the style of the Kubert–Lang theory of modular units; condition (iii) expresses invariance of the exponent vector under the unipotent action attached to $\Gamma_1(N)$, and (iv)–(v) say that the resulting order function is strictly minimised, among primitive pairs, at the classes $y=0$, $x = \pm 1$ and $y = \pm 1$. It is used to construct an auxiliary form on $X_1(N)$ whose cuspidal divisor is concentrated as required, in [`ModularCurve.SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd`](thm.html#ModularCurve.SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SiegelUnit_exists_peaked_exponent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.SiegelUnit.exists_peaked_exponent (N : ℕ) [NeZero N] (hN : 2 ≤ N) :
    ∃ (m : ZMod N → ZMod N → ℕ) (Ord : ZMod N → ZMod N → ℤ),
      (∀ x y : ZMod N, Ord x y =
        ∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
          (6 * (((r * x + s * y).val : ℕ) : ℤ) ^ 2
            - 6 * (N : ℤ) * (((r * x + s * y).val : ℕ) : ℤ) + (N : ℤ) ^ 2)) ∧
      m 0 0 = 0 ∧
      (∀ r s : ZMod N, m r (s + r) = m r s) ∧
      0 < Ord 1 0 ∧
      ∀ x y : ZMod N, (∃ a b : ZMod N, a * x + b * y = 1) →
        ¬ (y = 0 ∧ (x = 1 ∨ x = -1)) → ¬ (y = 1 ∨ y = -1) →
        Ord 1 0 < Ord x y := by sorry
