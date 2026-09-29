-- Prove2me | Theorems.Thm_GT_u3_step4
-- name    : GT.u3_step4
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:31:09.25306+00:00
-- url     : https://prove2.me/theorems/58ac4f8a-3373-4a4b-9285-0220bb63b071
-- title:
--   Theorem 9.5: a neighbourhood where the sets are locally pseudorandom
-- statement:
--   Let $R_0\le1$, $R_{t+1}\le\theta R_t$ with $0\le\theta\le1/16$, $S$ a frequency set, $W$ a weight on quadruples with $|W|\le B$ and $W\le1$, sets $A_1,\dots,A_4$, and suppose the $W$-average at level $0$ around $c_0$ is at least $c_3>0$. Under the numerical conditions of the statement (involving $\varepsilon,\mu>0$ and $K$), there are a centre $c$, $k<K$ and $T\supseteq S$ with $|T|\le|S|+k$ such that the $W$-average at level $20k$ around $c$ is at least $c_3/2$ and every balanced function $1_{A_i}-\alpha_i$ has local $U^2$ norm at most $\varepsilon$ on the corresponding Bohr neighbourhood.
--
--   **Notation.** Throughout, $p$ is a positive integer (usually a prime) and we work in $\mathbb{Z}/p\mathbb{Z}$. For a finite frequency set $S\subseteq\mathbb{Z}/p\mathbb{Z}$ we write $\|h\|_{S^\perp}=\max_{s\in S}\|sh/p\|_{\mathbb{R}/\mathbb{Z}}$ (and $0$ if $S=\emptyset$), $B(S,\rho)=\{x:\|x\|_{S^\perp}\le\rho\}$ for the Bohr set, and $P_{S,\rho}(a)=2\int_{1/2}^{1}\mu_{B(S,t\rho)}(a)\,dt$ for the *regular* probability distribution on $B(S,\rho)$, where $\mu_B$ is the uniform probability measure on $B$. We write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}/\mathbb{Z}$ and $e_p(x)=e(x/p)$ for $x\in\mathbb{Z}/p\mathbb{Z}$. A frequency $\ell$ is *$A$-good* for $T$ if $\|\ell h/p\|_{\mathbb{R}/\mathbb{Z}}\le A\|h\|_{T^\perp}$ for all $h$. All objects are those of the definition bundle `GreenTaoFourCore`.
--
--   **Formalization Note.** This is one node of a machine-checked decomposition of the proof of `Erdos142.green_tao_four` (Green–Tao's bound $r_4(N)\ll N(\log N)^{-c}$). All explicit numerical constants and the precise quantitative side conditions are exactly those of the Lean statement; the notation above is only a reading guide.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, Section 9, Theorem 9.5

import Mathlib
import Definitions.Def_GreenTaoFourCore

open Finset KM
open scoped ComplexConjugate
open Classical

namespace GT

theorem u3_step4 {p : ℕ} [NeZero p] {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) (hR1 : R 0 ≤ 1) (S : Finset (ZMod p))
    (W : (Fin 4 → ZMod p) → ℝ) {B : ℝ} (hW : ∀ q, |W q| ≤ B) (hW1 : ∀ q, W q ≤ 1)
    (A : Fin 4 → Finset (ZMod p)) (c0 : Fin 4 → ZMod p) {c3 ε mu : ℝ} {K : ℕ}
    (hc3 : 0 < c3) (hε : 0 < ε) (hmu : 0 < mu) (hQ0 : c3 ≤ QW R W S c0 0)
    (hmuε : 20 * mu ≤ c3 / 8 * (ε / 8) ^ 2 / 4) (hK : 1 + 20 * mu ≤ 20 * mu * K)
    (hθK : (B * 300 + c3 / 8 * 1600) * (S.card + K) * θ ≤ c3 / 8 * (ε / 8) ^ 2 / 4)
    (hsep : 7200 * (S.card + K) * θ ≤ (ε / 2) ^ 2)
    (herr : (350 * (S.card + K) + 13) * θ ≤ ε / 8) :
    ∃ (c : Fin 4 → ZMod p) (k : ℕ) (T : Finset (ZMod p)), S ⊆ T ∧ T.card ≤ S.card + k ∧
      k < K ∧ c3 / 2 ≤ QW R W T c (20 * k) ∧
      ∀ i, ∑ u, regP T (R (20 * k + lvl i)) (u - cent c i) *
        U2f T (R (20 * k + 10)) (R (20 * k + 11)) (bal R A T c (20 * k) i) u ≤ ε := by sorry

end GT
