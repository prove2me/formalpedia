-- Prove2me | Theorems.Thm_GT_ed_num_partA
-- name    : GT.ed_num_partA
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:30:23.264488+00:00
-- url     : https://prove2.me/theorems/c6e09803-9c62-4619-998f-9f8bc2ae1c47
-- title:
--   Numerical facts for Theorem 6.6: $p$ is large enough for the inverse theorem
-- statement:
--   Let $0<\eta\le1/10$, $t\le s$ with $s\le65\eta^{-3C_2}$, $\exp(-\eta^{-2C_5})\le\rho\le1$ and $p\ge\exp(\eta^{-3C_5})$. Put $\eta_i=(\eta/64)^8$, $\theta=\theta(s,\eta_i)$ the scale ratio of Theorem 8.1 and $\varepsilon_4=\exp(-\eta^{-C_4})$. Then
--
--   $$P\big(s,\eta_i,\theta,\theta\varepsilon_4\rho\big)\le p,$$
--
--   where $P(s,\eta,\theta,\rho_0)=(4/(\theta^{T(\eta)}\rho_0))^{4(s+\lfloor J(\eta)\rfloor+1)}\eta^{-2^{30}}$ is the largeness requirement on $p$ in Theorem 8.1.
--
--   **Notation.** Throughout, $p$ is a positive integer (usually a prime) and we work in $\mathbb{Z}/p\mathbb{Z}$. For a finite frequency set $S\subseteq\mathbb{Z}/p\mathbb{Z}$ we write $\|h\|_{S^\perp}=\max_{s\in S}\|sh/p\|_{\mathbb{R}/\mathbb{Z}}$ (and $0$ if $S=\emptyset$), $B(S,\rho)=\{x:\|x\|_{S^\perp}\le\rho\}$ for the Bohr set, and $P_{S,\rho}(a)=2\int_{1/2}^{1}\mu_{B(S,t\rho)}(a)\,dt$ for the *regular* probability distribution on $B(S,\rho)$, where $\mu_B$ is the uniform probability measure on $B$. We write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}/\mathbb{Z}$ and $e_p(x)=e(x/p)$ for $x\in\mathbb{Z}/p\mathbb{Z}$. A frequency $\ell$ is *$A$-good* for $T$ if $\|\ell h/p\|_{\mathbb{R}/\mathbb{Z}}\le A\|h\|_{T^\perp}$ for all $h$. All objects are those of the definition bundle `GreenTaoFourCore`.
--
--   **Formalization Note.** This is one node of a machine-checked decomposition of the proof of `Erdos142.green_tao_four` (Green–Tao's bound $r_4(N)\ll N(\log N)^{-c}$). All explicit numerical constants and the precise quantitative side conditions are exactly those of the Lean statement; the notation above is only a reading guide.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, Section 6 (proof of Theorem 6.6)

import Mathlib
import Definitions.Def_GreenTaoFourCore

open Finset KM

namespace GT

theorem ed_num_partA {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {s t : ℕ} (hts : t ≤ s)
    (hs : (s : ℝ) ≤ 65 * (1 / η) ^ (3 * C2))
    {ρ : ℝ} (hρ0 : Real.exp (-(1 / η) ^ (2 * C5)) ≤ ρ) (hρ1 : ρ ≤ 1) {p : ℕ}
    (hp : Real.exp ((1 / η) ^ (3 * C5)) ≤ p) :
    (u3P s (edηi η) (edθ s η) (edθ s η * SLA.eps4 η * ρ) ≤ p) := by sorry

end GT
