-- Prove2me | Theorems.Thm_GT_poor_d2
-- name    : GT.poor_d2
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:30:37.674981+00:00
-- url     : https://prove2.me/theorems/7d46aca0-130e-4f73-bbcd-d478e1d12066
-- title:
--   Proposition 7.1, first half: a poorly distributed label gives a large second-difference correlation
-- statement:
--   Let $S\subseteq\mathbb{Z}/p\mathbb{Z}$, $n_0\in\mathbb{Z}/p\mathbb{Z}$, $\rho>0$, $0<\varepsilon_4\le1/8$, $G$ a non-degenerate torus of dimension $d$, $F:G\to[-1,1]$ $1$-Lipschitz, and $\Xi$ locally quadratic on $n_0+B(S,\rho)$. Let $0<\eta\le1$ with $100|S|\varepsilon_4\le\delta_W/2$, where $\delta_W=\delta_W(G,\eta)$ is the Weyl correlation. Suppose the label is poorly distributed:
--
--   $$\mathbb{E}\,\prod_{i=0}^3F(\Xi(a+ir))<\big(\mathbb{E}\,F(\Xi(a))\big)^4-\eta/2,$$
--
--   with $a-n_0\sim P_{S,\rho/2}$ and $r\sim P_{S,\varepsilon_4\rho}$. Then there is a non-zero $k\in\mathbb{Z}^d$ with $|k_i|<4M_i$, a point $a_0$ with $\|a_0-n_0\|_{S^\perp}\le\rho/2$, and $1$-bounded $b_1,b_2$ with
--
--   $$\frac{\delta_W}{4}\le\Big|\sum_{r,h}P_{S,\varepsilon_4\rho}(r)P_{S,\rho_h}(h)\,b_1(r)b_2(h)\,e\big(\Delta^2(k\cdot\Xi)(a_0;r,h)\big)\Big|.$$
--
--   **Notation.** Throughout, $p$ is a positive integer (usually a prime) and we work in $\mathbb{Z}/p\mathbb{Z}$. For a finite frequency set $S\subseteq\mathbb{Z}/p\mathbb{Z}$ we write $\|h\|_{S^\perp}=\max_{s\in S}\|sh/p\|_{\mathbb{R}/\mathbb{Z}}$ (and $0$ if $S=\emptyset$), $B(S,\rho)=\{x:\|x\|_{S^\perp}\le\rho\}$ for the Bohr set, and $P_{S,\rho}(a)=2\int_{1/2}^{1}\mu_{B(S,t\rho)}(a)\,dt$ for the *regular* probability distribution on $B(S,\rho)$, where $\mu_B$ is the uniform probability measure on $B$. We write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}/\mathbb{Z}$ and $e_p(x)=e(x/p)$ for $x\in\mathbb{Z}/p\mathbb{Z}$. A frequency $\ell$ is *$A$-good* for $T$ if $\|\ell h/p\|_{\mathbb{R}/\mathbb{Z}}\le A\|h\|_{T^\perp}$ for all $h$. All objects are those of the definition bundle `GreenTaoFourCore`.
--
--   **Formalization Note.** This is one node of a machine-checked decomposition of the proof of `Erdos142.green_tao_four` (Green–Tao's bound $r_4(N)\ll N(\log N)^{-c}$). All explicit numerical constants and the precise quantitative side conditions are exactly those of the Lean statement; the notation above is only a reading guide.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, Section 7, Proposition 7.1 (first half of the proof)

import Mathlib
import Definitions.Def_GreenTaoFourCore

open Finset KM
open scoped ComplexConjugate

namespace GT

theorem poor_d2 {p : ℕ} [NeZero p] {S : Finset (ZMod p)} {n0 : ZMod p} {ρ : ℝ} (hρ : 0 < ρ)
    {ε4 : ℝ} (hε0 : 0 < ε4) (hε8 : ε4 ≤ 1 / 8)
    {G : DTorus} (hG : G.Good) {F : G.Pt → ℝ} (hF : G.IsLip F) (hF1 : ∀ x, |F x| ≤ 1)
    {Ξ : ZMod p → G.Pt} (hL : LocQuad (sBohr S n0 ρ) Ξ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hsmall : 100 * S.card * ε4 ≤ wδ G η / 2)
    (hpoor : ∑ z : ZMod p × ZMod p, regP S (ρ / 2) (z.1 - n0) * regP S (ε4 * ρ) z.2 *
        (F (Ξ z.1) * F (Ξ (z.1 + z.2)) * F (Ξ (z.1 + 2 * z.2)) * F (Ξ (z.1 + 3 * z.2))) <
      (∑ z : ZMod p × ZMod p, regP S (ρ / 2) (z.1 - n0) * regP S (ε4 * ρ) z.2 *
        F (Ξ z.1)) ^ 4 - η / 2) :
    ∃ kφ : Fin G.d → ℤ, kφ ≠ 0 ∧ (∀ i, |kφ i| < 4 * wM G η i) ∧
      ∃ a0, snorm S (a0 - n0) ≤ ρ / 2 ∧
      ∃ b1 b2 : ZMod p → ℂ, (∀ r, ‖b1 r‖ ≤ 1) ∧ (∀ h, ‖b2 h‖ ≤ 1) ∧
        wδ G η / 4 ≤ ‖∑ r, ∑ h, (regP S (ε4 * ρ) r : ℂ) * (regP S (wρh S G η ε4 ρ) h : ℂ) *
          (b1 r * b2 h * ec (D2 (fun x => kdot kφ (Ξ x)) a0 r h))‖ := by sorry

end GT
