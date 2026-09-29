-- Prove2me | Theorems.Thm_GT_u3_step5
-- name    : GT.u3_step5
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:31:35.752243+00:00
-- url     : https://prove2.me/theorems/c8362ea8-77e0-480a-a578-19d7edd6e954
-- title:
--   Theorem 9.7: good points and the new frequency map
-- statement:
--   Let $R_{t+1}\le\theta R_t$ with $0\le\theta\le1/16$, sets $A_i$ whose balanced functions have local $U^2$ norm at most $\varepsilon_4$ around a centre $c$ at level $j$, and suppose the average of the penalised weight $W=W_{S,\rho_v,L,\xi,A}$ (with $|W|\le B$) at this neighbourhood is at least $c_4>0$, together with the smallness conditions of the statement. Then $c_4/4\le\alpha_1\alpha_2\alpha_3\alpha_4$, and there are a set $G_d$ of good points and a map $\xi'$ such that the measure of the complement of $G_d$ is at most $2/(Lt)+1700(\sqrt{\varepsilon_4}+200|T|\theta)/c_4^2$, and for $a\in G_d$ one has $|g_{12}(a)-\alpha_1\alpha_2|\le\alpha_1\alpha_2/10$ and the density of very bad pairs $\xi'(a)-\xi(a-a_2)-\xi(a_2)$ is at most $2t\alpha_1\alpha_2$.
--
--   **Notation.** Throughout, $p$ is a positive integer (usually a prime) and we work in $\mathbb{Z}/p\mathbb{Z}$. For a finite frequency set $S\subseteq\mathbb{Z}/p\mathbb{Z}$ we write $\|h\|_{S^\perp}=\max_{s\in S}\|sh/p\|_{\mathbb{R}/\mathbb{Z}}$ (and $0$ if $S=\emptyset$), $B(S,\rho)=\{x:\|x\|_{S^\perp}\le\rho\}$ for the Bohr set, and $P_{S,\rho}(a)=2\int_{1/2}^{1}\mu_{B(S,t\rho)}(a)\,dt$ for the *regular* probability distribution on $B(S,\rho)$, where $\mu_B$ is the uniform probability measure on $B$. We write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}/\mathbb{Z}$ and $e_p(x)=e(x/p)$ for $x\in\mathbb{Z}/p\mathbb{Z}$. A frequency $\ell$ is *$A$-good* for $T$ if $\|\ell h/p\|_{\mathbb{R}/\mathbb{Z}}\le A\|h\|_{T^\perp}$ for all $h$. All objects are those of the definition bundle `GreenTaoFourCore`.
--
--   **Formalization Note.** This is one node of a machine-checked decomposition of the proof of `Erdos142.green_tao_four` (Green–Tao's bound $r_4(N)\ll N(\log N)^{-c}$). All explicit numerical constants and the precise quantitative side conditions are exactly those of the Lean statement; the notation above is only a reading guide.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, Section 9, Theorem 9.7

import Mathlib
import Definitions.Def_GreenTaoFourCore

open Finset KM
open scoped ComplexConjugate
open Classical

namespace GT

theorem u3_step5 {p : ℕ} [NeZero p] {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) {T : Finset (ZMod p)} {A : Fin 4 → Finset (ZMod p)} {c : Fin 4 → ZMod p} {j : ℕ} {ε4 : ℝ} (hPR : ∀ i, ∑ u, regP T (R (j + lvl i)) (u - cent c i) *
    U2f T (R (j + 10)) (R (j + 11)) (bal R A T c j i) u ≤ ε4) (S : Finset (ZMod p)) (ρv L : ℝ) (ξ : ZMod p → ZMod p) {B : ℝ}
    (hWB : ∀ q, |Wt S ρv L ξ A q| ≤ B) {c4 t : ℝ} (hc4 : 0 < c4) (ht : 0 < t) (hL : 0 < L)
    (hQ : c4 ≤ QW R (Wt S ρv L ξ A) T c j) (h1 : B * (50 * T.card * θ) ≤ c4 / 2)
    (h2 : 2 * √(√ε4 + 200 * T.card * θ) ≤ c4 / 4) :
    ∃ (Gd : Finset (ZMod p)) (ξ' : ZMod p → ZMod p),
      c4 / 4 ≤ alph R A T c j 0 * alph R A T c j 1 * (alph R A T c j 2 * alph R A T c j 3) ∧
      ∑ a, regP T (R j) (a - aC c) * (if a ∈ Gd then 0 else 1) ≤
        2 / (L * t) + 1700 * (√ε4 + 200 * T.card * θ) / c4 ^ 2 ∧
      ∀ a ∈ Gd, |g12 R A T c j a - alph R A T c j 0 * alph R A T c j 1| ≤
          alph R A T c j 0 * alph R A T c j 1 / 10 ∧
        ∑ x2, regP T (R (j + 2)) x2 * (I12 A a (cent c 1 + x2) *
          vb S ρv (ξ' a - ξ (a - (cent c 1 + x2)) - ξ (cent c 1 + x2))) ≤
          2 * t * (alph R A T c j 0 * alph R A T c j 1) := by sorry

end GT
