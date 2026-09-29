-- Prove2me | Theorems.Thm_GT_u3_back
-- name    : GT.u3_back
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:31:00.848792+00:00
-- url     : https://prove2.me/theorems/0b7221d2-1d72-4f38-821f-bf961e1ed1c9
-- title:
--   Steps seven to nine of the proof of Theorem 8.1
-- statement:
--   Let $p$ be prime, $S\subseteq T$ with $S$ containing a non-zero element, $f$ $1$-bounded, and $\xi''$ approximately linear on $T$-scale $R_l$ (defects $B$-good). Suppose that for some $a_0$ with $\|a_0\|_{S^\perp}\le\sigma_0$, some $\xi_0$ and $c_0>0$,
--
--   $$c_0\le\sum_nP_{T,r'}(n)\sum_{n_0}P_{S,\rho_0}(n_0)\Big|\sum_mP_{T,\rho_4}(m)\,f(n_0+m+a_0-n)\overline{f(n_0+m)}\,e_p\big((\xi''(n)-\xi_0)m\big)\Big|^2,$$
--
--   and that the scales $\rho_0,r',r_3,\rho_A,\rho_4,\dots,\rho_{10}$ satisfy the separation conditions of the statement. Then there are $1\le q\le\bar q$, a locally quadratic phase $\phi$ on $B(T,2\rho_{10})$ and $\beta$ with
--
--   $$\frac{c_0^4}{4096}\le\sum_nP_{S,\rho_0}(n)\Big|\sum_mP_{T,\rho_{10}}(m)f(n+2qm)\,e\big(-\phi(m)-\beta(n)m/p\big)\Big|.$$
--
--   **Notation.** Throughout, $p$ is a positive integer (usually a prime) and we work in $\mathbb{Z}/p\mathbb{Z}$. For a finite frequency set $S\subseteq\mathbb{Z}/p\mathbb{Z}$ we write $\|h\|_{S^\perp}=\max_{s\in S}\|sh/p\|_{\mathbb{R}/\mathbb{Z}}$ (and $0$ if $S=\emptyset$), $B(S,\rho)=\{x:\|x\|_{S^\perp}\le\rho\}$ for the Bohr set, and $P_{S,\rho}(a)=2\int_{1/2}^{1}\mu_{B(S,t\rho)}(a)\,dt$ for the *regular* probability distribution on $B(S,\rho)$, where $\mu_B$ is the uniform probability measure on $B$. We write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}/\mathbb{Z}$ and $e_p(x)=e(x/p)$ for $x\in\mathbb{Z}/p\mathbb{Z}$. A frequency $\ell$ is *$A$-good* for $T$ if $\|\ell h/p\|_{\mathbb{R}/\mathbb{Z}}\le A\|h\|_{T^\perp}$ for all $h$. All objects are those of the definition bundle `GreenTaoFourCore`.
--
--   **Formalization Note.** This is one node of a machine-checked decomposition of the proof of `Erdos142.green_tao_four` (Green–Tao's bound $r_4(N)\ll N(\log N)^{-c}$). All explicit numerical constants and the precise quantitative side conditions are exactly those of the Lean statement; the notation above is only a reading guide.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, proof of Theorem 8.1 (steps seven to nine)

import Mathlib
import Definitions.Def_GreenTaoFourCore

open Finset KM
open scoped ComplexConjugate

namespace GT

theorem u3_back {p : ℕ} [NeZero p] (hp : p.Prime) {S T : Finset (ZMod p)} (hS : ∃ s ∈ S, s ≠ 0) (hST : S ⊆ T)
    (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (ξ'' : ZMod p → ZMod p) {B Rl : ℝ} (hB : 0 ≤ B)
    (hlin : ∀ x y, snorm T x ≤ Rl → snorm T y ≤ Rl → Good T B (ξ'' (x + y) - ξ'' x - ξ'' y))
    (a0 ξ0 : ZMod p) {σ0 : ℝ} (ha0 : snorm S a0 ≤ σ0)
    {ρ0 r' r3 ρA ρ4 ρ5 ρ6 ρ9 ρ10 c0 : ℝ}
    (hρ0 : 0 < ρ0) (hr' : 0 < r') (hr3 : 0 < r3) (hρA : 0 < ρA) (hρ4 : 0 < ρ4) (hρ5 : 0 < ρ5)
    (hρ6 : 0 < ρ6) (hρ9 : 0 < ρ9) (hρ10 : 0 < ρ10) (hc0 : 0 < c0)
    (hQ : c0 ≤ ∑ n, regP T r' n * ∑ n0, regP S ρ0 n0 *
      ‖∑ m, (regP T ρ4 m : ℂ) * (f (n0 + m + (a0 - n)) * conj (f (n0 + m))) *
        ech ((ξ'' n - ξ0) * m)‖ ^ 2)
    -- seventh step
    (h54 : 4 * ρ5 ≤ ρ4) (h6r : 4 * ρ6 ≤ r') (h40 : 4 * ρ4 ≤ ρ0) (hR : r' + ρ6 ≤ Rl)
    (hE7 : err7 S T B ρ0 r' r3 ρ4 ρ5 ρ6 ≤ c0 / 2)
    -- the bilinear form
    (hb1 : 4 * (2 ^ (T.card ^ 2) * T.card) * ρA ≤ r3)
    (hb2 : (2 * T.card + 1) * (2 ^ (T.card ^ 2) * T.card) * ρA + r3 ≤ Rl)
    (hb3 : 2 * T.card * (2 ^ (T.card ^ 2) * T.card) * ρA < 1)
    (hb4 : 4 * B * ρA < 1)
    -- eighth step
    (h65 : 8 * ρ6 ≤ ρ5) (h5A : 4 * ρ5 ≤ ρA) (hδ : 100 * T.card * ρ6 / ρ5 ≤ (c0 / 2) ^ 2 / 2)
    (h9R : ρ9 ≤ lqR T.card (del8 T c0 ρ5 ρ6 ^ 4) ρ6)
    (h10R : ρ10 ≤ lqR T.card (del8 T c0 ρ5 ρ6 ^ 4) ρ6)
    -- ninth step
    (h10 : 4 * ((2 * qbar T c0 ρ5 ρ6) * ρ10) ≤ ρ5) (h9 : 4 * ((2 * qbar T c0 ρ5 ρ6) * ρ9) ≤ ρ6)
    (hA : ρ6 + ρ5 + (2 * qbar T c0 ρ5 ρ6) * (ρ9 + ρ10) ≤ ρA)
    (hE9 : err9 T c0 ρ5 ρ6 ρ9 ρ10 ≤ c0 / 4)
    (h109 : 4 * ρ10 ≤ ρ9) (hsep : 7200 * T.card * ρ10 ≤ ((c0 / 4) ^ 2 / 2) ^ 2 * ρ9)
    (hA' : 2 * (ρ9 + ρ10) ≤ ρA) (hLQ : 16 * ρ10 ≤ ρA)
    (hsh : 4 * (σ0 + r' + ρ5 + ρ6 + (2 * qbar T c0 ρ5 ρ6) * ρ9) ≤ ρ0)
    (hfin : 50 * S.card * (σ0 + r' + ρ5 + ρ6 + (2 * qbar T c0 ρ5 ρ6) * ρ9) / ρ0 ≤
      ((c0 / 4) ^ 2) ^ 2 / 16) :
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ qbar T c0 ρ5 ρ6 ∧
      ∃ (φ : ZMod p → UnitAddCircle) (β : ZMod p → ZMod p),
        LocQuad (sBohr T 0 (2 * ρ10)) φ ∧
        c0 ^ 4 / 4096 ≤ ∑ n, regP S ρ0 n * ‖∑ m, (regP T ρ10 m : ℂ) *
          (f (n + ((2 * q : ℕ) : ZMod p) * m) * ec (-(φ m) - ZMod.toAddCircle (β n * m)))‖ := by sorry

end GT
