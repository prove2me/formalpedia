-- Prove2me | Theorems.Thm_GT_u3_front
-- name    : GT.u3_front
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:31:27.29788+00:00
-- url     : https://prove2.me/theorems/ce5f49dc-ebfa-4e30-ae61-fbecc3e1387b
-- title:
--   Steps one to three of the proof of Theorem 8.1
-- statement:
--   Let $p$ be prime, $S$ non-empty, $0<\eta\le1$, scales $\rho_0,\dots,\rho_4,\rho_h,\rho_v$, $L\ge1$ and $m\ge1$ satisfying the separation conditions of the statement, and $f$ $1$-bounded with $\eta\le|\mathrm{U}^3_{S;\rho_0,\rho_1,\rho_2}(f)|$ (the local $U^3$ average). Then there are a set $\Omega\subseteq B(S,2\rho_2)$ of differences $D$, a frequency map $\xi$ with
--
--   $$\frac{\eta}{8}\le\sum_{n_0}P_{S,\rho_0}(n_0)\Big|\sum_{n_1}P_{S,\rho_1}(n_1)f(n_0+n_1+D)\overline{f(n_0+n_1)}e_p(-\xi(D)n_1)\Big|^2\quad(D\in\Omega),$$
--
--   sets $A_1,\dots,A_4\subseteq\Omega$ and a centre $c$ such that the penalised weight $W(q)=1_{q\in A}\,(1-L\,1_{\sigma_\xi(q)\text{ not }1/\rho_v\text{-good}})$ has quadruple average at least $10^{-6m}\eta^8 2^{-26}/4$.
--
--   **Notation.** Throughout, $p$ is a positive integer (usually a prime) and we work in $\mathbb{Z}/p\mathbb{Z}$. For a finite frequency set $S\subseteq\mathbb{Z}/p\mathbb{Z}$ we write $\|h\|_{S^\perp}=\max_{s\in S}\|sh/p\|_{\mathbb{R}/\mathbb{Z}}$ (and $0$ if $S=\emptyset$), $B(S,\rho)=\{x:\|x\|_{S^\perp}\le\rho\}$ for the Bohr set, and $P_{S,\rho}(a)=2\int_{1/2}^{1}\mu_{B(S,t\rho)}(a)\,dt$ for the *regular* probability distribution on $B(S,\rho)$, where $\mu_B$ is the uniform probability measure on $B$. We write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}/\mathbb{Z}$ and $e_p(x)=e(x/p)$ for $x\in\mathbb{Z}/p\mathbb{Z}$. A frequency $\ell$ is *$A$-good* for $T$ if $\|\ell h/p\|_{\mathbb{R}/\mathbb{Z}}\le A\|h\|_{T^\perp}$ for all $h$. All objects are those of the definition bundle `GreenTaoFourCore`.
--
--   **Formalization Note.** This is one node of a machine-checked decomposition of the proof of `Erdos142.green_tao_four` (Green–Tao's bound $r_4(N)\ll N(\log N)^{-c}$). All explicit numerical constants and the precise quantitative side conditions are exactly those of the Lean statement; the notation above is only a reading guide.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, Section 9 (steps one to three of the proof of Theorem 8.1)

import Mathlib
import Definitions.Def_GreenTaoFourCore

open Finset KM
open scoped ComplexConjugate
open Classical

namespace GT

theorem u3_front {p : ℕ} [NeZero p] (hp : p.Prime) {S : Finset (ZMod p)} (hS : S.Nonempty)
    {η ρ0 ρ1 ρ2 ρ3 ρ4 ρh ρv L : ℝ} {m : ℕ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hρ0 : 0 < ρ0) (hρ1 : 0 < ρ1) (hρ2 : 0 < ρ2) (hρ3 : 0 < ρ3) (hρ4 : 0 < ρ4)
    (h10 : 4 * ρ1 ≤ ρ0) (h20 : 4 * ρ2 ≤ ρ0) (h21 : 4 * ρ2 ≤ ρ1) (h32 : 8 * ρ3 ≤ ρ2)
    (h43 : ρ4 ≤ ρ3) (hρ21 : ρ2 ≤ 1)
    (hsep1 : 7200 * S.card * ρ1 ≤ (η / 4) ^ 2 * ρ0) (hsep2 : 100 * S.card * ρ2 ≤ η / 2 * ρ0)
    (hsep3 : 50 * S.card * ρ2 / ρ1 ≤ η ^ 2 / 64)
    (hsep4 : 150 * S.card * ρ3 / ρ2 ≤ η ^ 8 / 2 ^ 26)
    (hρh : 0 < ρh) (hρv : 0 < ρv) (h2v : 2 * ρv ≤ ρh)
    (hAρ : 13 * S.card / (ρ1 * (η ^ 8 / 2 ^ 25)) * ρh ≤ 1 / 1000)
    (hAv : 13 * S.card / (ρ1 * (η ^ 8 / 2 ^ 25)) ≤ 1 / ρv)
    (hL : 1 ≤ L) (hm : 1 ≤ m) (hpm : (10 : ℝ) ^ 60 * m ^ 10 ≤ p)
    (he : 50 * S.card * (ρv / 2) / ρh ≤ 1 / (4 * m))
    (hmL : 16 * L ≤ 2 ^ m * (η ^ 8 / 2 ^ 26))
    (hNG : (4 * (gM m : ℝ)) ^ 3 * (1 / (p * (ρ4 / 4) ^ S.card)) ≤
      (1 / 10 ^ 6) ^ m * (η ^ 8 / 2 ^ 26) / (8 * L))
    (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hU : η ≤ ‖u3avg S ρ0 ρ1 ρ2 f‖) :
    ∃ (Ω : Finset (ZMod p)) (ξ : ZMod p → ZMod p) (As : Fin 4 → Finset (ZMod p))
      (c : Fin 4 → ZMod p),
      (∀ D ∈ Ω, D ∈ bohr S (2 * ρ2)) ∧
      (∀ D ∈ Ω, η / 8 ≤ ∑ n0, regP S ρ0 n0 *
        ‖∑ n1, (regP S ρ1 n1 : ℂ) * (f (n0 + n1 + D) * conj (f (n0 + n1))) *
          ech (-(ξ D * n1))‖ ^ 2) ∧
      (∀ i, As i ⊆ Ω) ∧
      (1 / 10 ^ 6) ^ m * (η ^ 8 / 2 ^ 26) / 4 ≤ qavg S ρ4 ρ3 ρ2 c (Wt S ρv L ξ As) := by sorry

end GT
