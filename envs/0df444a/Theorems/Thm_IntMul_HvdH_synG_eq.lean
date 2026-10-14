-- Prove2me | Theorems.Thm_IntMul_HvdH_synG_eq
-- name    : IntMul.HvdH.synG_eq
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T01:31:39.155316+00:00
-- url     : https://prove2.me/theorems/7b521b0d-6d75-43ea-9ce1-0e4c6d7b58aa
-- title:
--   The radix-2 recursion computes the synthetic DFT over C[y]/(y^r+1)
-- statement:
--   Let $R=\mathbb C[y]/(y^r+1)$ with $r\ge1$, and let $t=2^e$ divide $2r$, so that $y^{2r/t}$ is a principal $t$-th root of unity in $R$. Let $u\in R^t$ be stored as coefficient arrays $u(k,c)$. Then the radix-2 Cooley–Tukey recursion `synG r e` (`IntMul_HvdH_SynFFT`) computes the normalised synthetic DFT
--   $$(\mathcal G_t u)_j=\frac1t\sum_{k=0}^{t-1}y^{-2rjk/t}\,u_k,\qquad 0\le j<t.$$
--   In coefficients: for $0\le c<r$ the coefficient of $y^c$ in entry $j$ equals the corresponding coefficient on the right, where `yShift r m` multiplies by $y^m$. This is the correctness half of Lemma 3.2 of Harvey–van der Hoeven.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 3.2

import Definitions.Def_IntMul_HvdH_SynFFT

namespace IntMul.HvdH
theorem synG_eq (r e : ℕ) (hr : 0 < r) (he : 2 ^ e ∣ 2 * r) (u : ℕ × ℕ → ℂ) (j c : ℕ)
    (hj : j < 2 ^ e) (hc : c < r) :
    synG r e u (j, c) = (1 / 2 ^ e : ℂ) * ∑ k ∈ Finset.range (2 ^ e),
      yShift r (-((2 * r / 2 ^ e * j * k : ℕ) : ℤ)) (fun c' => u (k, c')) c := by sorry
end IntMul.HvdH
