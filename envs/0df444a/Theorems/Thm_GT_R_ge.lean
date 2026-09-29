-- Prove2me | Theorems.Thm_GT_R_ge
-- name    : GT.R_ge
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:30:05.907444+00:00
-- url     : https://prove2.me/theorems/c21c89be-da0c-45f5-9779-3e6ca6b42f62
-- title:
--   Numerical bound: the radius of Proposition 7.1 is at least $\rho\exp(-2\eta^{-C_4})$
-- statement:
--   Under the same hypotheses as the companion bound on $K$ (namely $0<\eta\le1/10$, $S$ non-empty with $|S|\le65\eta^{-3C_2}$, $G$ a non-degenerate torus with $\dim G\le 64\eta^{-2C_2}$ and $\mathrm{vol}(G)\le\exp(\eta^{-2C_3})$, $\varepsilon_4=\exp(-\eta^{-C_4})$ and $\rho>0$), the radius $R=R(S,G,\eta,\varepsilon_4,\rho)$ on which the bilinear bound of Proposition 7.1 holds satisfies
--
--   $$\rho\,\exp\big(-2\eta^{-C_4}\big)\le R.$$
--
--   This lower bound on the scale is used in the parameter bookkeeping of the dimension-decrement step (Theorem 6.7).
--
--   **Notation.** Throughout, $p$ is a positive integer (usually a prime) and we work in $\mathbb{Z}/p\mathbb{Z}$. For a finite frequency set $S\subseteq\mathbb{Z}/p\mathbb{Z}$ we write $\|h\|_{S^\perp}=\max_{s\in S}\|sh/p\|_{\mathbb{R}/\mathbb{Z}}$ (and $0$ if $S=\emptyset$), $B(S,\rho)=\{x:\|x\|_{S^\perp}\le\rho\}$ for the Bohr set, and $P_{S,\rho}(a)=2\int_{1/2}^{1}\mu_{B(S,t\rho)}(a)\,dt$ for the *regular* probability distribution on $B(S,\rho)$, where $\mu_B$ is the uniform probability measure on $B$. We write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}/\mathbb{Z}$ and $e_p(x)=e(x/p)$ for $x\in\mathbb{Z}/p\mathbb{Z}$. A frequency $\ell$ is *$A$-good* for $T$ if $\|\ell h/p\|_{\mathbb{R}/\mathbb{Z}}\le A\|h\|_{T^\perp}$ for all $h$. All objects are those of the definition bundle `GreenTaoFourCore`.
--
--   **Formalization Note.** This is one node of a machine-checked decomposition of the proof of `Erdos142.green_tao_four` (Green–Tao's bound $r_4(N)\ll N(\log N)^{-c}$). All explicit numerical constants and the precise quantitative side conditions are exactly those of the Lean statement; the notation above is only a reading guide.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, Section 7 (parameters of Proposition 7.1)

import Mathlib
import Definitions.Def_GreenTaoFourCore

open Finset KM

namespace GT

theorem R_ge {p : ℕ} [NeZero p] {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {S : Finset (ZMod p)} (hSne : S.Nonempty) {G : DTorus} (hG : G.Good) (hs : (S.card : ℝ) ≤ 65 * (1 / η) ^ (3 * C2)) (hd : (G.d : ℝ) ≤ 64 * (1 / η) ^ (2 * C2)) (hV : G.vol ≤ Real.exp ((1 / η) ^ (2 * C3))) {ρ : ℝ} (hρ0 : 0 < ρ) : ρ * Real.exp (-2 * (1 / η) ^ C4) ≤ p71R S G η (SLA.eps4 η) ρ := by sorry

end GT
