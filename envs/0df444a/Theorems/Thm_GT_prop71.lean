-- Prove2me | Theorems.Thm_GT_prop71
-- name    : GT.prop71
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:30:45.616565+00:00
-- url     : https://prove2.me/theorems/35024676-ad35-46d9-95ae-3807ababa061
-- title:
--   Proposition 7.1: poorly distributed labels have a linearly-small quadratic direction
-- statement:
--   Let $p$ be prime, $S$ with a non-zero element, $n_0$, $\rho>0$, $0<\varepsilon_4\le1/8$, $G$ a non-degenerate torus, $F:G\to[-1,1]$ $1$-Lipschitz, $\Xi$ locally quadratic on $n_0+B(S,\rho)$, $0<\eta\le1$, $100|S|\varepsilon_4\le\delta_W/2$, and suppose the label is poorly distributed (as in the first half). Then there are a primitive $k\in\mathbb{Z}^d$ with $|k_i|<4M_i$ and a multiplier $1\le m\le m_{\max}$ such that for every $a$ with $\|a-n_0\|_{S^\perp}\le\rho/2$ there is a frequency $\xi$ with
--
--   $$\big\|k\cdot(\Xi(b+2mh)-\Xi(b))\big\|\le\big(2+2E+4mKR\big)\,\|h\|_{(S\cup\{\xi\})^\perp}$$
--
--   whenever $\|b-a\|_{S^\perp}\le R$, $\|h\|_{(S\cup\{\xi\})^\perp}\le R$ and $8m\|h\|_{(S\cup\{\xi\})^\perp}\le\rho$.
--
--   **Notation.** Throughout, $p$ is a positive integer (usually a prime) and we work in $\mathbb{Z}/p\mathbb{Z}$. For a finite frequency set $S\subseteq\mathbb{Z}/p\mathbb{Z}$ we write $\|h\|_{S^\perp}=\max_{s\in S}\|sh/p\|_{\mathbb{R}/\mathbb{Z}}$ (and $0$ if $S=\emptyset$), $B(S,\rho)=\{x:\|x\|_{S^\perp}\le\rho\}$ for the Bohr set, and $P_{S,\rho}(a)=2\int_{1/2}^{1}\mu_{B(S,t\rho)}(a)\,dt$ for the *regular* probability distribution on $B(S,\rho)$, where $\mu_B$ is the uniform probability measure on $B$. We write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}/\mathbb{Z}$ and $e_p(x)=e(x/p)$ for $x\in\mathbb{Z}/p\mathbb{Z}$. A frequency $\ell$ is *$A$-good* for $T$ if $\|\ell h/p\|_{\mathbb{R}/\mathbb{Z}}\le A\|h\|_{T^\perp}$ for all $h$. All objects are those of the definition bundle `GreenTaoFourCore`.
--
--   **Formalization Note.** This is one node of a machine-checked decomposition of the proof of `Erdos142.green_tao_four` (Green–Tao's bound $r_4(N)\ll N(\log N)^{-c}$). All explicit numerical constants and the precise quantitative side conditions are exactly those of the Lean statement; the notation above is only a reading guide.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, Section 7, Proposition 7.1

import Mathlib
import Definitions.Def_GreenTaoFourCore

open Finset KM
open scoped ComplexConjugate

namespace GT

theorem prop71 {p : ℕ} [NeZero p] (hp : p.Prime) {S : Finset (ZMod p)} (hS : ∃ s ∈ S, s ≠ 0) {n0 : ZMod p} {ρ : ℝ}
    (hρ : 0 < ρ) {ε4 : ℝ} (hε0 : 0 < ε4) (hε8 : ε4 ≤ 1 / 8)
    {G : DTorus} (hG : G.Good) {F : G.Pt → ℝ} (hF : G.IsLip F) (hF1 : ∀ x, |F x| ≤ 1)
    {Ξ : ZMod p → G.Pt} (hL : LocQuad (sBohr S n0 ρ) Ξ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hsmall : 100 * S.card * ε4 ≤ wδ G η / 2)
    (hpoor : ∑ z : ZMod p × ZMod p, regP S (ρ / 2) (z.1 - n0) * regP S (ε4 * ρ) z.2 *
        (F (Ξ z.1) * F (Ξ (z.1 + z.2)) * F (Ξ (z.1 + 2 * z.2)) * F (Ξ (z.1 + 3 * z.2))) <
      (∑ z : ZMod p × ZMod p, regP S (ρ / 2) (z.1 - n0) * regP S (ε4 * ρ) z.2 *
        F (Ξ z.1)) ^ 4 - η / 2) :
    ∃ k : Fin G.d → ℤ, Prim k ∧ (∀ i, |k i| < 4 * wM G η i) ∧
      ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ p71m S G η ∧
        ∀ a, snorm S (a - n0) ≤ ρ / 2 → ∃ ξ : ZMod p, ∀ b h : ZMod p,
          snorm S (b - a) ≤ p71R S G η ε4 ρ →
          snorm (insert ξ S) h ≤ p71R S G η ε4 ρ → 8 * m * snorm (insert ξ S) h ≤ ρ →
          ‖kdot k (Ξ (b + ((2 * m : ℕ) : ZMod p) * h) - Ξ b)‖ ≤
            (2 + 2 * p71E S G η ε4 ρ + 4 * m * p71K S G η ε4 ρ * p71R S G η ε4 ρ) *
              snorm (insert ξ S) h := by sorry

end GT
