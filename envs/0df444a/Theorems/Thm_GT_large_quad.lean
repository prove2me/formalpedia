-- Prove2me | Theorems.Thm_GT_large_quad
-- name    : GT.large_quad
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:30:30.492878+00:00
-- url     : https://prove2.me/theorems/6885efcf-ee1e-469b-a846-efc010d171c0
-- title:
--   Proposition 4.9: large local quadratic exponential sums
-- statement:
--   Let $p$ be prime, $S$ containing a non-zero element, $d=|S|$, $0<\rho\le\rho_1$ and $0<\delta\le1$. Let $\phi(n,m)\in\mathbb{R}/\mathbb{Z}$ be additive in each variable on the scale $2\rho_1$, and $\lambda,\mu$ additive on that scale. If
--
--   $$\delta\le\Big|\sum_{n,m}P_{S,\rho_1}(n)P_{S,\rho}(m)\,e\big(\phi(n,m)+\lambda(n)+\mu(m)\big)\Big|,$$
--
--   then there is an integer $1\le k\le(32/\delta)^{d^2}$ such that $\|k\phi(n,m)\|_{\mathbb{R}/\mathbb{Z}}\le K\,\|n\|_{S^\perp}\|m\|_{S^\perp}$ whenever $\|n\|_{S^\perp},\|m\|_{S^\perp}\le R$, with explicit $R=R(d,\delta,\rho)$ and $K=K(d,\delta,\rho)$.
--
--   **Notation.** Throughout, $p$ is a positive integer (usually a prime) and we work in $\mathbb{Z}/p\mathbb{Z}$. For a finite frequency set $S\subseteq\mathbb{Z}/p\mathbb{Z}$ we write $\|h\|_{S^\perp}=\max_{s\in S}\|sh/p\|_{\mathbb{R}/\mathbb{Z}}$ (and $0$ if $S=\emptyset$), $B(S,\rho)=\{x:\|x\|_{S^\perp}\le\rho\}$ for the Bohr set, and $P_{S,\rho}(a)=2\int_{1/2}^{1}\mu_{B(S,t\rho)}(a)\,dt$ for the *regular* probability distribution on $B(S,\rho)$, where $\mu_B$ is the uniform probability measure on $B$. We write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}/\mathbb{Z}$ and $e_p(x)=e(x/p)$ for $x\in\mathbb{Z}/p\mathbb{Z}$. A frequency $\ell$ is *$A$-good* for $T$ if $\|\ell h/p\|_{\mathbb{R}/\mathbb{Z}}\le A\|h\|_{T^\perp}$ for all $h$. All objects are those of the definition bundle `GreenTaoFourCore`.
--
--   **Formalization Note.** This is one node of a machine-checked decomposition of the proof of `Erdos142.green_tao_four` (Green–Tao's bound $r_4(N)\ll N(\log N)^{-c}$). All explicit numerical constants and the precise quantitative side conditions are exactly those of the Lean statement; the notation above is only a reading guide.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, Section 4, Proposition 4.9

import Mathlib
import Definitions.Def_GreenTaoFourCore

open Finset KM

namespace GT

theorem large_quad {p : ℕ} [NeZero p] (hp : p.Prime) {S : Finset (ZMod p)} (hS : ∃ s ∈ S, s ≠ 0) {ρ1 ρ δ : ℝ}
    (hρ : 0 < ρ) (hρρ1 : ρ ≤ ρ1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {φ : ZMod p → ZMod p → UnitAddCircle} {lam mu : ZMod p → UnitAddCircle}
    (hφ1 : ∀ m, snorm S m ≤ 2 * ρ1 → AddOn S (2 * ρ1) (fun n => φ n m))
    (hφ2 : ∀ n, snorm S n ≤ 2 * ρ1 → AddOn S (2 * ρ1) (fun m => φ n m))
    (hlam : AddOn S (2 * ρ1) lam) (hmu : AddOn S (2 * ρ1) mu)
    (hsum : δ ≤ ‖∑ n, ∑ m, (regP S ρ1 n : ℂ) * (regP S ρ m : ℂ) * ec (φ n m + lam n + mu m)‖) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ (32 / δ) ^ (S.card ^ 2) ∧
      ∀ n m, snorm S n ≤ lqR S.card δ ρ → snorm S m ≤ lqR S.card δ ρ →
        ‖k • φ n m‖ ≤ lqK S.card δ ρ * snorm S n * snorm S m := by sorry

end GT
