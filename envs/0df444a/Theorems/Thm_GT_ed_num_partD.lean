-- Prove2me | Theorems.Thm_GT_ed_num_partD
-- name    : GT.ed_num_partD
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:30:18.155296+00:00
-- url     : https://prove2.me/theorems/fe839c87-c38b-4caf-99fc-73ef33e74d46
-- title:
--   Numerical facts for Theorem 6.6: dilation, scales, volume and decrement
-- statement:
--   Let $0<\eta\le1/10$, $t\le s$ with $s\le65\eta^{-3C_2}$, $d_2\le64\eta^{-2C_2}$, $\rho\ge\exp(-\eta^{-2C_5})$ and $p\ge\exp(\eta^{-3C_5})$. With $\eta_i=(\eta/64)^8$ and $\theta,T,K,\kappa$ the scale ratio, depth, dilation bound and correlation of Theorem 8.1 at parameter $\eta_i$, and $E=\eta^{C_3}/2$, the following hold:
--   1. $6K<p$;
--   2. $4K\theta^{T}\theta\varepsilon_4\rho\le\theta\varepsilon_4\rho$;
--   3. $24\theta\varepsilon_4\rho\le\rho/2$;
--   4. $16\cdot2^{d_2}\le\exp(\eta^{-C_3})$;
--   5. $4E+\eta^{C_2}\le 3\kappa^2\,(\eta/64)(\eta/16)$.
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

theorem ed_num_partD {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {s t d2 : ℕ} (hts : t ≤ s)
    (hs : (s : ℝ) ≤ 65 * (1 / η) ^ (3 * C2)) (hd2 : (d2 : ℝ) ≤ 64 * (1 / η) ^ (2 * C2))
    {ρ : ℝ} (hρ0 : Real.exp (-(1 / η) ^ (2 * C5)) ≤ ρ) {p : ℕ}
    (hp : Real.exp ((1 / η) ^ (3 * C5)) ≤ p) :
    (6 * edK s η < p) ∧
    (4 * (edK s η * (edθ s η ^ edT η * (edθ s η * SLA.eps4 η * ρ))) ≤ edθ s η * SLA.eps4 η * ρ) ∧
    (24 * (edθ s η * SLA.eps4 η * ρ) ≤ ρ / 2) ∧
    (16 * 2 ^ d2 ≤ Real.exp ((1 / η) ^ C3)) ∧
    (4 * edE η + η ^ C2 ≤ 3 * edκ η ^ 2 * (η / 16 / 4 * (η / 16))) := by sorry

end GT
