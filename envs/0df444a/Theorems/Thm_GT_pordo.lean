-- Prove2me | Theorems.Thm_GT_pordo
-- name    : GT.pordo
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:31:14.84097+00:00
-- url     : https://prove2.me/theorems/723db2d7-548f-4c87-910d-f0ddbde07028
-- title:
--   Proposition 9.8: $\xi'$ respects almost all additive quadruples
-- statement:
--   In the setting of the fifth/sixth steps of the proof of Theorem 8.1 — scales $R_{j}$ with $R_{j+1}\le\theta R_j$, $\theta\le1/16$, sets $A_1,\dots,A_4$ whose balanced functions have local $U^2$ norms at most $\varepsilon_4$, and a set $G_d$ of good points on which the new frequency map $\xi'$ agrees, apart from rare very bad quadruples, with $\xi(a-x)+\xi(x)$ — the proportion of triples $(h,a,b)$ in a Bohr neighbourhood for which $\xi'(a)-\xi'(a+h)-\xi'(b)+\xi'(b+h)$ is not $4/\rho_v$-good is at most
--
--   $$8(2t+e_5)+\frac{30\big(\sqrt{\sqrt{\varepsilon_4}+200|T|\theta}+150|T|\theta\big)}{(\alpha_1\alpha_2)^2}.$$
--
--   **Notation.** Throughout, $p$ is a positive integer (usually a prime) and we work in $\mathbb{Z}/p\mathbb{Z}$. For a finite frequency set $S\subseteq\mathbb{Z}/p\mathbb{Z}$ we write $\|h\|_{S^\perp}=\max_{s\in S}\|sh/p\|_{\mathbb{R}/\mathbb{Z}}$ (and $0$ if $S=\emptyset$), $B(S,\rho)=\{x:\|x\|_{S^\perp}\le\rho\}$ for the Bohr set, and $P_{S,\rho}(a)=2\int_{1/2}^{1}\mu_{B(S,t\rho)}(a)\,dt$ for the *regular* probability distribution on $B(S,\rho)$, where $\mu_B$ is the uniform probability measure on $B$. We write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}/\mathbb{Z}$ and $e_p(x)=e(x/p)$ for $x\in\mathbb{Z}/p\mathbb{Z}$. A frequency $\ell$ is *$A$-good* for $T$ if $\|\ell h/p\|_{\mathbb{R}/\mathbb{Z}}\le A\|h\|_{T^\perp}$ for all $h$. All objects are those of the definition bundle `GreenTaoFourCore`.
--
--   **Formalization Note.** This is one node of a machine-checked decomposition of the proof of `Erdos142.green_tao_four` (Green–Tao's bound $r_4(N)\ll N(\log N)^{-c}$). All explicit numerical constants and the precise quantitative side conditions are exactly those of the Lean statement; the notation above is only a reading guide.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, Section 9, Proposition 9.8

import Mathlib
import Definitions.Def_GreenTaoFourCore

open Finset KM
open scoped ComplexConjugate
open Classical

namespace GT

theorem pordo {p : ℕ} [NeZero p] {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) {T : Finset (ZMod p)} {A : Fin 4 → Finset (ZMod p)} {c : Fin 4 → ZMod p} {j : ℕ} {ε4 : ℝ} (hPR : ∀ i, ∑ u, regP T (R (j + lvl i)) (u - cent c i) *
    U2f T (R (j + 10)) (R (j + 11)) (bal R A T c j i) u ≤ ε4) (S : Finset (ZMod p)) (ρv : ℝ) (ξ ξ' : ZMod p → ZMod p) (Gd : Finset (ZMod p))
    {t e5 : ℝ} (ht : 0 ≤ t) (hpos : 0 < alph R A T c j 0 * alph R A T c j 1)
    (hGd1 : ∑ a, regP T (R j) (a - aC c) * (if a ∈ Gd then 0 else 1) ≤ e5)
    (hGd2 : ∀ a ∈ Gd, ∑ x, regP T (R (j + 2)) x * (I12 A a (cent c 1 + x) *
      vb S ρv (ξ' a - ξ (a - (cent c 1 + x)) - ξ (cent c 1 + x))) ≤
      2 * t * (alph R A T c j 0 * alph R A T c j 1)) :
    E3 R T c j (fun h a b => if Good S (4 / ρv) (ξ' a - ξ' (a + h) - ξ' b + ξ' (b + h))
      then 0 else 1) ≤
      8 * (2 * t + e5) + 30 * (√(√ε4 + 200 * T.card * θ) + 150 * T.card * θ) /
        (alph R A T c j 0 * alph R A T c j 1) ^ 2 := by sorry

end GT
