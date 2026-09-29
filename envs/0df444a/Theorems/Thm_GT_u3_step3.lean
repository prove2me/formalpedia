-- Prove2me | Theorems.Thm_GT_u3_step3
-- name    : GT.u3_step3
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:30:59.647764+00:00
-- url     : https://prove2.me/theorems/d0056cc5-01c7-4506-a664-aaf147dfa58e
-- title:
--   Theorem 9.4: sets on which very bad quadruples are rare
-- statement:
--   Let $p$ be prime, scales $0<r_2\le r_3\le r_4\le1$, $\rho_h,\rho_v>0$ with $2\rho_v\le\rho_h$, $A\ge0$ with $A\rho_h\le1/1000$ and $A\le1/\rho_v$, $c_G\ge0$, $L\ge1$, $m\ge1$ with $p\ge10^{60}m^{10}$ and the genericity conditions of the statement. If for a set $\Omega$, a map $\xi$ and a centre $c$ the proportion of additive quadruples $q$ (drawn around $c$ at scales $r_2,r_3,r_4$) with all $q_i\in\Omega$ and $\sigma_\xi(q)=\xi(q_1)+\xi(q_2)-\xi(q_3)-\xi(q_4)$ $A$-good is at least $c_G$, then there are $A_1,\dots,A_4\subseteq\Omega$ with
--
--   $$\frac{10^{-6m}c_G}{4}\le\mathbb{E}_q\,1_{q\in A_1\times\dots\times A_4}\big(1-L\cdot1_{\sigma_\xi(q)\text{ not }1/\rho_v\text{-good}}\big).$$
--
--   **Notation.** Throughout, $p$ is a positive integer (usually a prime) and we work in $\mathbb{Z}/p\mathbb{Z}$. For a finite frequency set $S\subseteq\mathbb{Z}/p\mathbb{Z}$ we write $\|h\|_{S^\perp}=\max_{s\in S}\|sh/p\|_{\mathbb{R}/\mathbb{Z}}$ (and $0$ if $S=\emptyset$), $B(S,\rho)=\{x:\|x\|_{S^\perp}\le\rho\}$ for the Bohr set, and $P_{S,\rho}(a)=2\int_{1/2}^{1}\mu_{B(S,t\rho)}(a)\,dt$ for the *regular* probability distribution on $B(S,\rho)$, where $\mu_B$ is the uniform probability measure on $B$. We write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}/\mathbb{Z}$ and $e_p(x)=e(x/p)$ for $x\in\mathbb{Z}/p\mathbb{Z}$. A frequency $\ell$ is *$A$-good* for $T$ if $\|\ell h/p\|_{\mathbb{R}/\mathbb{Z}}\le A\|h\|_{T^\perp}$ for all $h$. All objects are those of the definition bundle `GreenTaoFourCore`.
--
--   **Formalization Note.** This is one node of a machine-checked decomposition of the proof of `Erdos142.green_tao_four` (Green–Tao's bound $r_4(N)\ll N(\log N)^{-c}$). All explicit numerical constants and the precise quantitative side conditions are exactly those of the Lean statement; the notation above is only a reading guide.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, Section 9, Theorem 9.4

import Mathlib
import Definitions.Def_GreenTaoFourCore

open Finset KM
open scoped ComplexConjugate
open Classical

namespace GT

theorem u3_step3 {p : ℕ} [NeZero p] (hp : p.Prime) {S : Finset (ZMod p)} {r2 r3 r4 ρh ρv A cG L : ℝ}
    (hr2 : 0 < r2) (h23 : r2 ≤ r3) (h34 : r3 ≤ r4) (hr4 : r4 ≤ 1)
    (hρh : 0 < ρh) (hρv : 0 < ρv) (h2v : 2 * ρv ≤ ρh)
    (hA0 : 0 ≤ A) (hAρ : A * ρh ≤ 1 / 1000) (hAv : A ≤ 1 / ρv) (hcG : 0 ≤ cG)
    (hL : 1 ≤ L) {m : ℕ} (hm : 1 ≤ m) (hpm : (10 : ℝ) ^ 60 * m ^ 10 ≤ p)
    (he : 50 * S.card * (ρv / 2) / ρh ≤ 1 / (4 * m))
    (hmL : 16 * L ≤ 2 ^ m * cG)
    (hNG : (4 * (gM m : ℝ)) ^ 3 * (1 / (p * (r2 / 4) ^ S.card)) ≤ (1 / 10 ^ 6) ^ m * cG / (8 * L))
    (Ω : Finset (ZMod p)) (ξ : ZMod p → ZMod p) (c : Fin 4 → ZMod p)
    (hG : cG ≤ qavg S r2 r3 r4 c
      (fun q => if (∀ i, q i ∈ Ω) ∧ Good S A (sig ξ q) then 1 else 0)) :
    ∃ As : Fin 4 → Finset (ZMod p), (∀ i, As i ⊆ Ω) ∧
      (1 / 10 ^ 6) ^ m * cG / 4 ≤ qavg S r2 r3 r4 c (Wt S ρv L ξ As) := by sorry

end GT
