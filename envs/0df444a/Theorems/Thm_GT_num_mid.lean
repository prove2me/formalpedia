-- Prove2me | Theorems.Thm_GT_num_mid
-- name    : GT.num_mid
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:30:51.448568+00:00
-- url     : https://prove2.me/theorems/f4beccfd-605d-44b7-a799-6d927048cea0
-- title:
--   Numerical hypotheses of steps four to six of Theorem 8.1
-- statement:
--   Let $s_c\le s$, $0<\eta\le2^{-30}$, $0<\theta\le\theta(s,\eta)$ and $0<\rho_0\le1$. With $J=\eta^{-2^{24}}$, $K=\lfloor J\rfloor+1$, $\mu=1/(20\lfloor J\rfloor)$, $L=10^6$ and $c_3=c_3(\eta)$ the density obtained after the third step, a list of explicit numerical inequalities holds between these parameters and the scales $\theta^{j}\rho_0$; these are precisely the quantitative hypotheses under which steps four, five and six of the proof of the local inverse $U^3$ theorem (Theorems 9.5, 9.7 and Proposition 9.8) can be chained together.
--
--   **Notation.** Throughout, $p$ is a positive integer (usually a prime) and we work in $\mathbb{Z}/p\mathbb{Z}$. For a finite frequency set $S\subseteq\mathbb{Z}/p\mathbb{Z}$ we write $\|h\|_{S^\perp}=\max_{s\in S}\|sh/p\|_{\mathbb{R}/\mathbb{Z}}$ (and $0$ if $S=\emptyset$), $B(S,\rho)=\{x:\|x\|_{S^\perp}\le\rho\}$ for the Bohr set, and $P_{S,\rho}(a)=2\int_{1/2}^{1}\mu_{B(S,t\rho)}(a)\,dt$ for the *regular* probability distribution on $B(S,\rho)$, where $\mu_B$ is the uniform probability measure on $B$. We write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}/\mathbb{Z}$ and $e_p(x)=e(x/p)$ for $x\in\mathbb{Z}/p\mathbb{Z}$. A frequency $\ell$ is *$A$-good* for $T$ if $\|\ell h/p\|_{\mathbb{R}/\mathbb{Z}}\le A\|h\|_{T^\perp}$ for all $h$. All objects are those of the definition bundle `GreenTaoFourCore`.
--
--   **Formalization Note.** This is one node of a machine-checked decomposition of the proof of `Erdos142.green_tao_four` (Green–Tao's bound $r_4(N)\ll N(\log N)^{-c}$). All explicit numerical constants and the precise quantitative side conditions are exactly those of the Lean statement; the notation above is only a reading guide.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, Sections 8–9 (parameter choices in the proof of Theorem 8.1)

import Mathlib
import Definitions.Def_GreenTaoFourCore

open Finset KM

namespace GT

theorem num_mid {s sc : ℕ} (hsc : sc ≤ s) {η θ ρ0 : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2 ^ 30)
    (hθ0 : 0 < θ) (hθ : θ ≤ u3θ s η) (hρ0 : 0 < ρ0) (hρ01 : ρ0 ≤ 1) :
    0 < 1 / (20 * (⌊u3J η⌋₊ : ℝ)) ∧
    20 * (1 / (20 * (⌊u3J η⌋₊ : ℝ))) ≤ u3c3 η / 8 * (u3c3 η ^ 16 / 8) ^ 2 / 4 ∧
    1 + 20 * (1 / (20 * (⌊u3J η⌋₊ : ℝ))) ≤
      20 * (1 / (20 * (⌊u3J η⌋₊ : ℝ))) * ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ) ∧
    (u3L * 300 + u3c3 η / 8 * 1600) * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ ≤
      u3c3 η / 8 * (u3c3 η ^ 16 / 8) ^ 2 / 4 ∧
    7200 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ ≤ (u3c3 η ^ 16 / 2) ^ 2 ∧
    (350 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) + 13) * θ ≤ u3c3 η ^ 16 / 8 ∧
    u3L * (50 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ) ≤ u3c3 η / 4 ∧
    2 * √(√(u3c3 η ^ 16) + 200 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ) ≤ u3c3 η / 8 ∧
    2 / (u3L * (1 / 200)) + 1700 * (√(u3c3 η ^ 16) +
      200 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ) / (u3c3 η / 2) ^ 2 ≤ 1 / 1000 ∧
    30 * (√(√(u3c3 η ^ 16) + 200 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ) +
      150 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ) / (u3c3 η / 8) ^ 2 ≤ 1 / 1000 ∧
    4 * (θ ^ (20 * ⌊u3J η⌋₊ + 90) * ρ0) ≤ θ ^ (20 * (⌊u3J η⌋₊ + 1) + 2) * ρ0 ∧
    50 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * (θ ^ (20 * ⌊u3J η⌋₊ + 90) * ρ0) /
      (θ ^ (20 * (⌊u3J η⌋₊ + 1) + 2) * ρ0) ≤ 1 / 1000 ∧
    4 * (θ ^ 4 * (θ ^ (20 * ⌊u3J η⌋₊ + 90) * ρ0)) ≤ θ * ρ0 ∧
    2 * (50 * (sc : ℝ) * (θ ^ 4 * (θ ^ (20 * ⌊u3J η⌋₊ + 90) * ρ0)) / (θ * ρ0)) +
      50 * (sc : ℝ) * (θ * ρ0) / ρ0 +
      2 * (2 * Real.pi * (9 * (1 / (θ ^ 3 * ρ0)) * (θ ^ 4 * (θ ^ (20 * ⌊u3J η⌋₊ + 90) * ρ0))))
      ≤ η / 16 := by sorry

end GT
