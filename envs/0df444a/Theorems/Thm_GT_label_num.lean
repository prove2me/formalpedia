-- Prove2me | Theorems.Thm_GT_label_num
-- name    : GT.label_num
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:30:31.61153+00:00
-- url     : https://prove2.me/theorems/6f6614fe-93c2-4dba-bccf-a2a24e54f263
-- title:
--   Numerical facts for a poorly distributed label
-- statement:
--   Let $0<\eta\le1/10$, $S$ non-empty with $|S|\le65\eta^{-3C_2}$, $G$ a non-degenerate torus with $\dim G\le64\eta^{-2C_2}$ and $\mathrm{vol}(G)\le\exp(\eta^{-2C_3})$, and $0<\rho\le1$. Let $\varepsilon_4=\exp(-\eta^{-C_4})$, let $R$, $L_m$, $m_{\max}$ be the radius, Lipschitz constant and multiplier bound of Proposition 7.1, and $\tau=\rho\exp(-\eta^{-2C_4})$. Then all numerical conditions required to refine a poorly distributed label hold: $100|S|\varepsilon_4\le\delta_W/2$; $0<R$ and $4R\le\rho/2$; $0<\tau\le1$ and $\exp(-\eta^{-C_5})\rho\le\tau$; the volume factor $2^{d^2}\sum_i4M_i/\|v_i\|\le\exp(\eta^{-C_3})$; $m_{\max}\le\exp(\eta^{-C_4})$; and for every $1\le m\le m_{\max}$ and every integer vector $w$ with $|w_i|\le1+\sum_j4M_j$: $4m\tau\le R$, the translation errors are at most $\eta^{C_3}/4$, and $L_m(\tau/2)\,\|\sum_iw_iv_i\|\le\eta^{C_3}/4$.
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

theorem label_num {p : ℕ} [NeZero p] {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {S : Finset (ZMod p)}
    (hSne : S.Nonempty) {G : DTorus} (hG : G.Good)
    (hs : (S.card : ℝ) ≤ 65 * (1 / η) ^ (3 * C2)) (hd : (G.d : ℝ) ≤ 64 * (1 / η) ^ (2 * C2))
    (hV : G.vol ≤ Real.exp ((1 / η) ^ (2 * C3))) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    100 * S.card * SLA.eps4 η ≤ wδ G η / 2 ∧
    0 < p71R S G η (SLA.eps4 η) ρ ∧ 4 * p71R S G η (SLA.eps4 η) ρ ≤ ρ / 2 ∧
    0 < ρ * Real.exp (-(1 / η) ^ (2 * C4)) ∧ ρ * Real.exp (-(1 / η) ^ (2 * C4)) ≤ 1 ∧
    Real.exp (-(1 / η) ^ C5) * ρ ≤ ρ * Real.exp (-(1 / η) ^ (2 * C4)) ∧
    2 ^ (G.d ^ 2) * (∑ i, 4 * (wM G η i : ℝ) / ‖G.v i‖) ≤ Real.exp ((1 / η) ^ C3) ∧
    p71m S G η ≤ Real.exp ((1 / η) ^ C4) ∧
    ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ p71m S G η → ∀ w : Fin G.d → ℤ,
      (∀ i, |(w i : ℝ)| ≤ 1 + ∑ j, 4 * (wM G η j : ℝ)) →
      4 * (m * (ρ * Real.exp (-(1 / η) ^ (2 * C4)))) ≤ p71R S G η (SLA.eps4 η) ρ ∧
      50 * S.card * (m * (ρ * Real.exp (-(1 / η) ^ (2 * C4)))) / p71R S G η (SLA.eps4 η) ρ +
        50 * S.card * p71R S G η (SLA.eps4 η) ρ / (ρ / 2) ≤ η ^ C3 / 4 ∧
      p71L S G η (SLA.eps4 η) ρ m * (ρ * Real.exp (-(1 / η) ^ (2 * C4)) / 2) *
        ‖G.emb (fun i => (w i : ℝ))‖ ≤ η ^ C3 / 4 := by sorry

end GT
