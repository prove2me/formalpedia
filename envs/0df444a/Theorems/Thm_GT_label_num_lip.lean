-- Prove2me | Theorems.Thm_GT_label_num_lip
-- name    : GT.label_num_lip
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:30:40.832362+00:00
-- url     : https://prove2.me/theorems/6f1e9c6b-e84c-4600-a673-0f82b23a1ba0
-- title:
--   Numerical fact: the Lipschitz error of a refined label is at most $\eta^{C_3}/4$
-- statement:
--   Under the hypotheses of the numerical lemma for poorly distributed labels ($0<\eta\le1/10$, $S$ non-empty with $|S|\le65\eta^{-3C_2}$, $G$ non-degenerate with $\dim G\le64\eta^{-2C_2}$, $\mathrm{vol}(G)\le\exp(\eta^{-2C_3})$, $0<\rho\le1$), for every multiplier $1\le m\le m_{\max}(S,G,\eta)$ and every integer vector $w$ with $|w_i|\le1+\sum_j4M_j$ one has
--
--   $$L_m\cdot\frac{\rho\exp(-\eta^{-2C_4})}{2}\cdot\Big\|\sum_i w_iv_i\Big\|\le\frac{\eta^{C_3}}{4},$$
--
--   where $L_m$ is the Lipschitz constant in the conclusion of Proposition 7.1, $v_i$ the basis of $G$ and $M_i=\lceil1000(d+1)\|v_i\|/\eta\rceil$ the Weyl cut-offs.
--
--   **Notation.** Throughout, $p$ is a positive integer (usually a prime) and we work in $\mathbb{Z}/p\mathbb{Z}$. For a finite frequency set $S\subseteq\mathbb{Z}/p\mathbb{Z}$ we write $\|h\|_{S^\perp}=\max_{s\in S}\|sh/p\|_{\mathbb{R}/\mathbb{Z}}$ (and $0$ if $S=\emptyset$), $B(S,\rho)=\{x:\|x\|_{S^\perp}\le\rho\}$ for the Bohr set, and $P_{S,\rho}(a)=2\int_{1/2}^{1}\mu_{B(S,t\rho)}(a)\,dt$ for the *regular* probability distribution on $B(S,\rho)$, where $\mu_B$ is the uniform probability measure on $B$. We write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}/\mathbb{Z}$ and $e_p(x)=e(x/p)$ for $x\in\mathbb{Z}/p\mathbb{Z}$. A frequency $\ell$ is *$A$-good* for $T$ if $\|\ell h/p\|_{\mathbb{R}/\mathbb{Z}}\le A\|h\|_{T^\perp}$ for all $h$. All objects are those of the definition bundle `GreenTaoFourCore`.
--
--   **Formalization Note.** This is one node of a machine-checked decomposition of the proof of `Erdos142.green_tao_four` (Green–Tao's bound $r_4(N)\ll N(\log N)^{-c}$). All explicit numerical constants and the precise quantitative side conditions are exactly those of the Lean statement; the notation above is only a reading guide.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, Section 7 (proof of Theorem 6.7)

import Mathlib
import Definitions.Def_GreenTaoFourCore

open Finset KM

namespace GT

theorem label_num_lip {p : ℕ} [NeZero p] {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {S : Finset (ZMod p)}
    (hSne : S.Nonempty) {G : DTorus} (hG : G.Good)
    (hs : (S.card : ℝ) ≤ 65 * (1 / η) ^ (3 * C2)) (hd : (G.d : ℝ) ≤ 64 * (1 / η) ^ (2 * C2))
    (hV : G.vol ≤ Real.exp ((1 / η) ^ (2 * C3))) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ p71m S G η → ∀ w : Fin G.d → ℤ,
      (∀ i, |(w i : ℝ)| ≤ 1 + ∑ j, 4 * (wM G η j : ℝ)) →
      p71L S G η (SLA.eps4 η) ρ m * (ρ * Real.exp (-(1 / η) ^ (2 * C4)) / 2) *
        ‖G.emb (fun i => (w i : ℝ))‖ ≤ η ^ C3 / 4 := by sorry

end GT
