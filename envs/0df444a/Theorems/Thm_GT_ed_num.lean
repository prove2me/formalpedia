-- Prove2me | Theorems.Thm_GT_ed_num
-- name    : GT.ed_num
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:30:16.339464+00:00
-- url     : https://prove2.me/theorems/f0fab2ce-9bca-4059-89df-8f51611f3c4b
-- title:
--   Numerical facts for the energy-decrement step
-- statement:
--   Let $0<\eta\le1/10$, let $t\le s$ be natural numbers with $s\le65\eta^{-3C_2}$, let $d_2\le 64\eta^{-2C_2}$, let $\exp(-\eta^{-2C_5})\le\rho\le1$ and let $p\ge\exp(\eta^{-3C_5})$. Then all the numerical inequalities needed in the proof of Theorem 6.6 hold for these parameters, i.e. the structure `EdNum` $(\eta,s,t,d_2,\rho,p)$ holds. These include: $p$ is large enough to apply the local inverse $U^3$ theorem (Theorem 8.1) with parameter $(\eta/64)^8$ at scale $\theta\,\varepsilon_4\rho$; $p>6K$ where $K$ is the dilation bound of that theorem; the final scales are not too small compared with $\exp(-\eta^{-C_5})\rho$; $16\cdot 2^{d_2}\le\exp(\eta^{-C_3})$; and the energy decrement dominates the accumulated errors.
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

theorem ed_num {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {s t d2 : ℕ} (hts : t ≤ s)
    (hs : (s : ℝ) ≤ 65 * (1 / η) ^ (3 * C2)) (hd2 : (d2 : ℝ) ≤ 64 * (1 / η) ^ (2 * C2))
    {ρ : ℝ} (hρ0 : Real.exp (-(1 / η) ^ (2 * C5)) ≤ ρ) (hρ1 : ρ ≤ 1) {p : ℕ}
    (hp : Real.exp ((1 / η) ^ (3 * C5)) ≤ p) : EdNum η s t d2 ρ p := by sorry

end GT
