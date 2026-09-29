-- Prove2me | Theorems.Thm_GT_K_le
-- name    : GT.K_le
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:30:21.564622+00:00
-- url     : https://prove2.me/theorems/aa420fc0-b5b8-46b9-94c1-bd132f0ae9d8
-- title:
--   Numerical bound: $K\rho^2\le \exp(3\eta^{-C_4})$ for the bilinear constant of Proposition 7.1
-- statement:
--   Let $0<\eta\le 1/10$, let $S\subseteq\mathbb{Z}/p\mathbb{Z}$ be non-empty with $|S|\le 65\eta^{-3C_2}$, and let $G=\mathbb{R}^d/\Lambda$ be a non-degenerate (reduced) torus of dimension $d\le 64\eta^{-2C_2}$ and volume $\mathrm{vol}(G)\le\exp(\eta^{-2C_3})$. Let $\varepsilon_4=\exp(-\eta^{-C_4})$ and $\rho>0$. Then the constant $K=K(S,G,\eta,\varepsilon_4,\rho)$ of the bilinear bound in Proposition 7.1 satisfies
--
--   $$K\,\rho^{2}\le \exp\big(3\eta^{-C_4}\big).$$
--
--   Here $C_2=2^{32}<C_3=2^{64}<C_4=2^{256}<C_5=2^{1024}$ are the constants of the argument. This is one of the numerical estimates needed to verify the parameter bookkeeping in the dimension-decrement step (Theorem 6.7).
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

theorem K_le {p : ℕ} [NeZero p] {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {S : Finset (ZMod p)} (hSne : S.Nonempty) {G : DTorus} (hG : G.Good) (hs : (S.card : ℝ) ≤ 65 * (1 / η) ^ (3 * C2)) (hd : (G.d : ℝ) ≤ 64 * (1 / η) ^ (2 * C2)) (hV : G.vol ≤ Real.exp ((1 / η) ^ (2 * C3))) {ρ : ℝ} (hρ0 : 0 < ρ) : p71K S G η (SLA.eps4 η) ρ * ρ ^ 2 ≤ Real.exp (3 * (1 / η) ^ C4) := by sorry

end GT
