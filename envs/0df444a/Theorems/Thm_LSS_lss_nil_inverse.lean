-- Prove2me | Theorems.Thm_LSS_lss_nil_inverse
-- name    : LSS.lss_nil_inverse
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-28T18:07:55.901416+00:00
-- url     : https://prove2.me/theorems/d1d2984b-d39d-4013-bd5c-f8aeb900bec3
-- title:
--   Leng–Sah–Sawhney: quasi-polynomial inverse theorem for the $U^{s+1}[N]$ norm (nilsequence form)
-- statement:
--   Let $s\ge 3$. There is a constant $C=C_s>0$ such that the following holds. Let $N\ge 1$, $0<\delta\le 1/2$, and let $f:\mathbb Z\to[-1,1]$ be supported on $[N]=\{1,\dots,N\}$ with
--   $$\sum_{x\in[N]}\ \sum_{h_1,\dots,h_{s+1}\in(-N,N)}\ \prod_{\omega\in\{0,1\}^{s+1}} f(x+\omega\cdot h)\ \ge\ \delta^{2^{s+1}}N^{s+2}$$
--   (this is $\|f\|_{U^{s+1}[N]}\gg_s\delta$). Then there are a nilmanifold $G/\Gamma$ of degree $s$, dimension $d\le C(1+\log(1/\delta))^C$ and complexity at most $M=\exp(C(1+\log(1/\delta))^C)$, a polynomial sequence $g:\mathbb Z\to G$, and a function $F:G/\Gamma\to\mathbb C$ with $|F|\le M$ and Lipschitz constant at most $M$, such that
--   $$\Big|\sum_{n=1}^N f(n)\,F(g(n)\Gamma)\Big|\ \ge\ N/M.$$
--
--   This is the quasi-polynomial inverse theorem for the Gowers $U^{s+1}[N]$ norm of Leng, Sah and Sawhney (Theorem 1.2 of arXiv:2402.17994), specialised to real-valued $f$, with the Gowers norm written as an unnormalised sum. Nilmanifolds, complexity, polynomial sequences and the Lipschitz condition are as in the definition file `LSSNil` (the Green–Tao / Leng–Sah–Sawhney conventions).
--
--   **Formalization note.** The hypothesis is `gowersZ N (s+1) f ≥ δ^(2^(s+1)) N^(s+2)`. Since the number of $(s+1)$-dimensional parallelepipeds in $[N]$ is at most $2^{s+1}N^{s+2}$, it implies $\|f\|_{U^{s+1}[N]}\ge\delta/2$, and Theorem 1.2 is then applied with $\delta/2$.
-- source:
--   J. Leng, A. Sah, M. Sawhney, Quasipolynomial bounds for the inverse theorem for the Gowers U^{s+1}[N]-norm, arXiv:2402.17994, Theorem 1.2 (p. 1)

import Mathlib
import Definitions.Def_LSSInterface
import Definitions.Def_LSSNil

open Finset

namespace LSS

theorem lss_nil_inverse (s : ℕ) (hs : 3 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (δ : ℝ) (f : ℤ → ℝ), 0 < δ → δ ≤ 1 / 2 → (∀ x, |f x| ≤ 1) →
      SupportedOn N f → δ ^ (2 ^ (s + 1)) * (N : ℝ) ^ (s + 2) ≤ gowersZ N (s + 1) f →
      ∃ (G : Nilmanifold s) (g : ℤ → G.Mat) (F : G.Mat → ℂ),
        (G.d : ℝ) ≤ C * (1 + Real.log (1 / δ)) ^ C ∧ G.complexity ≤ qp C (1 / δ) ∧
        G.IsPoly g ∧ G.IsLip (qp C (1 / δ)) F ∧
        (N : ℝ) / qp C (1 / δ) ≤ ‖∑ x ∈ Icc (1 : ℤ) N, (f x : ℂ) * F (g x)‖ := by sorry

end LSS
