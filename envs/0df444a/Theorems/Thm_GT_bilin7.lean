-- Prove2me | Theorems.Thm_GT_bilin7
-- name    : GT.bilin7
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:30:43.604268+00:00
-- url     : https://prove2.me/theorems/d62b9604-d374-4d9a-939e-673d8964a2f2
-- title:
--   From an approximately linear frequency map to an exactly bilinear phase
-- statement:
--   Let $p$ be prime, $T\subseteq\mathbb{Z}/p\mathbb{Z}$ containing a non-zero element, $d=|T|$, and let $B\ge0$, $r_3,\rho_A>0$, $R$ satisfy the smallness conditions of the statement (e.g. $4\cdot 2^{d^2}d\,\rho_A\le r_3$ and $4B\rho_A<1$). Suppose $\xi'':\mathbb{Z}/p\mathbb{Z}\to\mathbb{Z}/p\mathbb{Z}$ is approximately linear: for all $x,y$ with $\|x\|_{T^\perp},\|y\|_{T^\perp}\le R$, the defect $\xi''(x+y)-\xi''(x)-\xi''(y)$ is $B$-good for $T$. Then there is $\Xi:(\mathbb{Z}/p\mathbb{Z})^2\to\mathbb{R}/\mathbb{Z}$ which is additive in each variable on the scale $\rho_A$ (in the second variable for every $n$; in the first for $\|n\|_{T^\perp}\le\rho_A$), and such that for $\|n\|_{T^\perp},\|m\|_{T^\perp}\le\rho_A$
--
--   $$\Big\|\Xi(n,m)-\frac{\xi''(n)m}{p}\Big\|_{\mathbb{R}/\mathbb{Z}}\le B\,\|m\|_{T^\perp}\Big(\frac{50\,d^2\,2^{d^2}d\,\|n\|_{T^\perp}}{r_3}+1\Big).$$
--
--   This is the algebraic part of the seventh step of the proof of the local inverse $U^3$ theorem.
--
--   **Notation.** Throughout, $p$ is a positive integer (usually a prime) and we work in $\mathbb{Z}/p\mathbb{Z}$. For a finite frequency set $S\subseteq\mathbb{Z}/p\mathbb{Z}$ we write $\|h\|_{S^\perp}=\max_{s\in S}\|sh/p\|_{\mathbb{R}/\mathbb{Z}}$ (and $0$ if $S=\emptyset$), $B(S,\rho)=\{x:\|x\|_{S^\perp}\le\rho\}$ for the Bohr set, and $P_{S,\rho}(a)=2\int_{1/2}^{1}\mu_{B(S,t\rho)}(a)\,dt$ for the *regular* probability distribution on $B(S,\rho)$, where $\mu_B$ is the uniform probability measure on $B$. We write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}/\mathbb{Z}$ and $e_p(x)=e(x/p)$ for $x\in\mathbb{Z}/p\mathbb{Z}$. A frequency $\ell$ is *$A$-good* for $T$ if $\|\ell h/p\|_{\mathbb{R}/\mathbb{Z}}\le A\|h\|_{T^\perp}$ for all $h$. All objects are those of the definition bundle `GreenTaoFourCore`.
--
--   **Formalization Note.** This is one node of a machine-checked decomposition of the proof of `Erdos142.green_tao_four` (Green–Tao's bound $r_4(N)\ll N(\log N)^{-c}$). All explicit numerical constants and the precise quantitative side conditions are exactly those of the Lean statement; the notation above is only a reading guide.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, proof of Theorem 8.1 (seventh step)

import Mathlib
import Definitions.Def_GreenTaoFourCore

open Finset KM

namespace GT

theorem bilin7 {p : ℕ} [NeZero p] (hp : p.Prime) {T : Finset (ZMod p)} (hT : ∃ s ∈ T, s ≠ 0) {B R r3 ρA : ℝ}
    (hB : 0 ≤ B) (hr3 : 0 < r3) (hρA : 0 < ρA)
    (h1 : 4 * (2 ^ (T.card ^ 2) * T.card) * ρA ≤ r3)
    (h2 : (2 * T.card + 1) * (2 ^ (T.card ^ 2) * T.card) * ρA + r3 ≤ R)
    (h3 : 2 * T.card * (2 ^ (T.card ^ 2) * T.card) * ρA < 1)
    (h4 : 4 * B * ρA < 1) (ξ'' : ZMod p → ZMod p)
    (hlin : ∀ x y, snorm T x ≤ R → snorm T y ≤ R → Good T B (ξ'' (x + y) - ξ'' x - ξ'' y)) :
    ∃ Ξ : ZMod p → ZMod p → UnitAddCircle,
      (∀ m, AddOn T ρA (fun n => Ξ n m)) ∧
      (∀ n, snorm T n ≤ ρA → AddOn T ρA (fun m => Ξ n m)) ∧
      ∀ n m, snorm T n ≤ ρA → snorm T m ≤ ρA →
        ‖Ξ n m - ZMod.toAddCircle (ξ'' n * m)‖ ≤
          B * snorm T m * (50 * T.card * T.card * (2 ^ (T.card ^ 2) * T.card) * snorm T n / r3
            + 1) := by sorry

end GT
