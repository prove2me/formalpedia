-- Prove2me | Theorems.Thm_GT_u3_mid
-- name    : GT.u3_mid
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:30:52.609027+00:00
-- url     : https://prove2.me/theorems/fe0c0bfe-0ad5-44f5-9d8d-3f6f804c1c06
-- title:
--   Steps four to six of the proof of Theorem 8.1
-- statement:
--   Given the output of the first three steps (a set $\Omega$ of differences with large local Fourier coefficients at frequencies $\xi(D)$, sets $A_i\subseteq\Omega$ and a centre with quadruple average $\ge c_3$ of the penalised weight), and scales satisfying the numerical conditions of the statement, there are $T\supseteq S$ with $|T|\le|S|+k$, $k<K$, a map $\xi''$ whose linearity defects on $B(T,r/2)$ are $24/\rho_v$-good, a point $a_0$ with $\|a_0\|_{S^\perp}\le2\rho_2+r'$ and $\xi_0$ such that
--
--   $$\frac{c_3\eta}{288}\le\sum_nP_{T,r'}(n)\sum_{n_0}P_{S,\rho_0}(n_0)\Big|\sum_mP_{T,\rho_4}(m)f(n_0+m+a_0-n)\overline{f(n_0+m)}e_p\big((\xi''(n)-\xi_0)m\big)\Big|^2.$$
--
--   **Notation.** Throughout, $p$ is a positive integer (usually a prime) and we work in $\mathbb{Z}/p\mathbb{Z}$. For a finite frequency set $S\subseteq\mathbb{Z}/p\mathbb{Z}$ we write $\|h\|_{S^\perp}=\max_{s\in S}\|sh/p\|_{\mathbb{R}/\mathbb{Z}}$ (and $0$ if $S=\emptyset$), $B(S,\rho)=\{x:\|x\|_{S^\perp}\le\rho\}$ for the Bohr set, and $P_{S,\rho}(a)=2\int_{1/2}^{1}\mu_{B(S,t\rho)}(a)\,dt$ for the *regular* probability distribution on $B(S,\rho)$, where $\mu_B$ is the uniform probability measure on $B$. We write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}/\mathbb{Z}$ and $e_p(x)=e(x/p)$ for $x\in\mathbb{Z}/p\mathbb{Z}$. A frequency $\ell$ is *$A$-good* for $T$ if $\|\ell h/p\|_{\mathbb{R}/\mathbb{Z}}\le A\|h\|_{T^\perp}$ for all $h$. All objects are those of the definition bundle `GreenTaoFourCore`.
--
--   **Formalization Note.** This is one node of a machine-checked decomposition of the proof of `Erdos142.green_tao_four` (Green–Tao's bound $r_4(N)\ll N(\log N)^{-c}$). All explicit numerical constants and the precise quantitative side conditions are exactly those of the Lean statement; the notation above is only a reading guide.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, Section 9 (steps four to six of the proof of Theorem 8.1)

import Mathlib
import Definitions.Def_GreenTaoFourCore

open Finset KM
open scoped ComplexConjugate
open Classical

namespace GT

theorem u3_mid {p : ℕ} [NeZero p] {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) (hR1 : R 0 ≤ 1)
    {S : Finset (ZMod p)} (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {ρ0 ρ1 ρ2 η : ℝ} (hη : 0 < η) (hρ1 : 0 < ρ1) (hρ2 : 0 ≤ ρ2)
    (Ω : Finset (ZMod p)) (ξ : ZMod p → ZMod p) (hΩb : ∀ D ∈ Ω, D ∈ bohr S (2 * ρ2))
    (hΩ : ∀ D ∈ Ω, η / 8 ≤ ∑ n0, regP S ρ0 n0 *
      ‖∑ n1, (regP S ρ1 n1 : ℂ) * (f (n0 + n1 + D) * conj (f (n0 + n1))) *
        ech (-(ξ D * n1))‖ ^ 2)
    (As : Fin 4 → Finset (ZMod p)) (hAs : ∀ i, As i ⊆ Ω) {ρv L : ℝ} (hρv : 0 < ρv) (hL : 1 ≤ L)
    (c0 : Fin 4 → ZMod p) {c3 ε mu : ℝ} {K : ℕ}
    (hc3 : 0 < c3) (hε : 0 < ε) (hmu : 0 < mu) (hQ0 : c3 ≤ QW R (Wt S ρv L ξ As) S c0 0)
    -- fourth step
    (hmuε : 20 * mu ≤ c3 / 8 * (ε / 8) ^ 2 / 4) (hK : 1 + 20 * mu ≤ 20 * mu * K)
    (hθK : (L * 300 + c3 / 8 * 1600) * (S.card + K) * θ ≤ c3 / 8 * (ε / 8) ^ 2 / 4)
    (hsep : 7200 * (S.card + K) * θ ≤ (ε / 2) ^ 2)
    (herr : (350 * (S.card + K) + 13) * θ ≤ ε / 8)
    -- fifth step
    (h5a : L * (50 * (S.card + K) * θ) ≤ c3 / 4)
    (h5b : 2 * √(√ε + 200 * (S.card + K) * θ) ≤ c3 / 8)
    (h5c : 2 / (L * (1 / 200)) + 1700 * (√ε + 200 * (S.card + K) * θ) / (c3 / 2) ^ 2 ≤ 1 / 1000)
    (hep : 30 * (√(√ε + 200 * (S.card + K) * θ) + 150 * (S.card + K) * θ) / (c3 / 8) ^ 2 ≤
      1 / 1000)
    -- sixth step and Proposition 9.10
    {r r' ρ4 : ℝ} (hr' : 0 < r') (hr'r : r' ≤ r) (hr4 : 4 * r ≤ R (20 * K))
    (hrK : 50 * (S.card + K) * r / R (20 * K) ≤ 1 / 1000)
    (hρ4 : 0 < ρ4) (h41 : 4 * ρ1 ≤ ρ0) (h44 : 4 * ρ4 ≤ ρ1)
    (hz : 2 * (50 * S.card * ρ4 / ρ1) + 50 * S.card * ρ1 / ρ0 + 2 * (2 * Real.pi * (9 * (1 / ρv) * ρ4))
      ≤ η / 16) :
    ∃ (T : Finset (ZMod p)) (k : ℕ) (ξ'' : ZMod p → ZMod p) (a0 ξ0 : ZMod p),
      S ⊆ T ∧ T.card ≤ S.card + k ∧ k < K ∧
      (∀ x y, snorm T x ≤ r / 2 → snorm T y ≤ r / 2 →
        Good T (24 * (1 / ρv)) (ξ'' (x + y) - ξ'' x - ξ'' y)) ∧
      snorm S a0 ≤ 2 * ρ2 + r' ∧
      c3 * η / 288 ≤ ∑ n, regP T r' n * ∑ n0, regP S ρ0 n0 *
        ‖∑ m, (regP T ρ4 m : ℂ) * (f (n0 + m + (a0 - n)) * conj (f (n0 + m))) *
          ech ((ξ'' n - ξ0) * m)‖ ^ 2 := by sorry

end GT
