-- Prove2me | Theorems.Thm_IntMul_HvdH_parameters_5_1
-- name    : IntMul.HvdH.parameters_5_1
-- status  : Proved
-- author  : @avi
-- created : 2026-10-09T01:44:22.765214+00:00
-- url     : https://prove2.me/theorems/7914771b-6037-4809-a62d-a3343cc28e21
-- title:
--   HvdH §5.1 — parameter estimates (5.1)–(5.9)
-- statement:
--   Let $d\ge2$ and $n\ge n_0:=2^{d^{12}}$. Define
--   $$b:=\lceil\log_2n\rceil,\quad p:=6b,\quad\alpha:=\big\lceil(12d^2b)^{1/4}\big\rceil,\quad\gamma:=2d\alpha^2,$$
--   let $T$ be the power of two with $4n/b\le T<8n/b$, and let $r$ be the power of two with $T^{1/d}\le r<2T^{1/d}$. Then:
--
--   - (5.1), (5.2): $b\ge d^{12}\ge4096$ and $p\ge100$;
--   - (5.4): $2\le\alpha<2b^{7/24}<p^{1/2}$;
--   - (5.5): $\gamma<8b^{2/3}$;
--   - (5.8): $r\ge2^{d^{10}}$;
--   - (5.9): $T<n\le2^b$ and $T<2^p$;
--   - the factorisation: there is $0\le d'<d$ with $T=(r/2)^{d'}\,r^{d-d'}$ (so $T=t_1\cdots t_d$ with $t_1=\dots=t_{d'}=r/2$ and $t_{d'+1}=\dots=t_d=r$), and $r\ge4$, so every $t_i\ge2$.
--
--   Formalization note: $\lceil\log_2n\rceil$ is `Nat.clog 2 n`; real powers are `Real.rpow`; $r/2$ is natural-number division (exact, since $r\ge4$ is a power of two). $T$ and $r$ are universally quantified but uniquely determined by the hypotheses.
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), https://doi.org/10.4007/annals.2021.193.2.4 (preprint https://hal.science/hal-02070778v2), §5 preamble and §5.1 Parameter selection, equations (5.1), (5.2), (5.3), (5.4), (5.5), (5.6), (5.7), (5.8), (5.9) and the factorisation T = t1···td, pp. 36–37.

import Mathlib

namespace IntMul.HvdH

theorem parameters_5_1 (d : ℕ) (hd : 2 ≤ d) (n : ℕ) (hn : 2 ^ (d ^ 12) ≤ n)
    (b p α γ T r : ℕ) (hb : b = Nat.clog 2 n) (hp : p = 6 * b)
    (hα : α = ⌈((12 * d ^ 2 * b : ℕ) : ℝ) ^ ((1 : ℝ) / 4)⌉₊) (hγ : γ = 2 * d * α ^ 2)
    (hTpow : ∃ k : ℕ, T = 2 ^ k) (hT1 : 4 * (n : ℝ) / b ≤ T) (hT2 : (T : ℝ) < 8 * (n : ℝ) / b)
    (hrpow : ∃ j : ℕ, r = 2 ^ j) (hr1 : (T : ℝ) ^ ((1 : ℝ) / d) ≤ r)
    (hr2 : (r : ℝ) < 2 * (T : ℝ) ^ ((1 : ℝ) / d)) :
    -- (5.1), (5.2)
    (d ^ 12 ≤ b ∧ 4096 ≤ b ∧ 100 ≤ p) ∧
    -- (5.4)
    (2 ≤ α ∧ (α : ℝ) < 2 * (b : ℝ) ^ ((7 : ℝ) / 24) ∧
      2 * (b : ℝ) ^ ((7 : ℝ) / 24) < Real.sqrt p) ∧
    -- (5.5)
    (γ : ℝ) < 8 * (b : ℝ) ^ ((2 : ℝ) / 3) ∧
    -- (5.8)
    2 ^ (d ^ 10) ≤ r ∧
    -- (5.9)
    (T < n ∧ n ≤ 2 ^ b ∧ T < 2 ^ p) ∧
    -- the factorisation `T = t₁ ⋯ t_d` with `t₁ = ⋯ = t_{d'} = r/2`, `t_{d'+1} = ⋯ = t_d = r`
    (∃ d' : ℕ, d' < d ∧ (r / 2) ^ d' * r ^ (d - d') = T) ∧ 4 ≤ r := by sorry

end IntMul.HvdH
