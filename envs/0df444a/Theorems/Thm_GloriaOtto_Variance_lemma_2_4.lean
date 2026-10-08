-- Prove2me | Theorems.Thm_GloriaOtto_Variance_lemma_2_4
-- name    : GloriaOtto.Variance.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:19.835432+00:00
-- url     : https://prove2.me/theorems/5692ad32-02cf-4cc0-ae1f-353b113d43f8
-- title:
--   Lemma 2.4 — ∂φ_T(x)/∂a(e) = −(∇_iφ_T(z) + ξ_i)∇_{z_i}G_T(z,x), the bounds (2.13) on ∂[φ_T^{n+1}]/∂a(e), and (2.14)
-- statement:
--   Let $d \ge 2$, $0 < \alpha \le \beta$. For $a \in \mathcal A_{\alpha\beta}$, $T > 0$, $\xi \in \mathbb R^d$ with $|\xi| = 1$ and an edge $e = [z, z+e_i]$, write $a^{e\to t}$ for $a$ with the value on $e$ replaced by $t$, and $\nabla_{z_i}G_T(z,x) = G_T(z+e_i,x) - G_T(z,x)$.
--
--   1. (2.12) For every $x$, $t \mapsto \phi_T(x; a^{e\to t})$ is differentiable at $t = a(e)$ with
--   $$\frac{\partial\phi_T(x;a)}{\partial a(e)} = -\big(\nabla_i\phi_T(z;a) + \xi_i\big)\nabla_{z_i}G_T(z,x;a).$$
--   2. (2.13) For every $n \in \mathbb N$ there is $C_n$ (depending on $n, d, \alpha, \beta$ only) such that for all $a, T, \xi, e, x$ as above and every value $t \in [\alpha,\beta]$ of $a(e)$, the map $s \mapsto \phi_T(x;a^{e\to s})^{n+1}$ is differentiable at $t$ with derivative $D$ satisfying
--   $$|D| \le C_n\Big(|\phi_T(x;a)|^n\big(|\nabla_i\phi_T(z;a)|+1\big)|\nabla_{z_i}G_T(z,x;a)| + \big(|\nabla_i\phi_T(z;a)|+1\big)^{n+1}|\nabla_{z_i}G_T(z,x;a)|^{n+1}\Big).$$
--   3. (2.14) There is $C$ (depending on $d, \alpha, \beta$ only) such that for all $a, T, \xi, e$ and every $t \in [\alpha,\beta]$,
--   $$|\nabla_i\phi_T(z;a^{e\to t})| \le C\big(|\nabla_i\phi_T(z;a)| + 1\big).$$
--
--   These formulas relate the susceptibility of the approximate corrector to the Green's function, uniformly in the value of the perturbed coefficient. They feed Lemma 2.3 in the proofs of Proposition 2.1 and Theorem 2.1.
--
--   **Formalization Note.** The statement is pathwise: the i.i.d. assumption of the paper plays no role in it. "$\sup_{a(e)}$" is rendered by quantifying over every value $t\in[\alpha,\beta]$, with the right-hand sides evaluated at the unperturbed $a$; the differentiability in (2.13) is part of the conclusion.
-- source:
--   Gloria, Otto, arXiv:1104.1291v1, Lemma 2.4, (2.12)–(2.14), p. 16

import Mathlib
import Definitions.Def_GloriaOtto_Variance_Setup

open MeasureTheory ProbabilityTheory

namespace GloriaOtto.Variance

theorem lemma_2_4 (d : ℕ) (hd : 2 ≤ d) (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) :
    (∀ a : Edge d → ℝ, InA α β a → ∀ T : ℝ, 0 < T → ∀ ξ : Fin d → ℝ, sqNorm ξ = 1 →
      ∀ (z : Site d) (i : Fin d) (x : Site d),
        HasDerivAt (fun t => phiT (Function.update a (z, i) t) T ξ x)
          (-(grad (phiT a T ξ) z i + ξ i) * (greenT a T (z + unit i) x - greenT a T z x))
          (a (z, i))) ∧
    (∀ n : ℕ, ∃ C : ℝ, ∀ a : Edge d → ℝ, InA α β a → ∀ T : ℝ, 0 < T →
      ∀ ξ : Fin d → ℝ, sqNorm ξ = 1 → ∀ (z : Site d) (i : Fin d) (x : Site d),
        ∀ t ∈ Set.Icc α β, ∃ D : ℝ,
          HasDerivAt (fun s => phiT (Function.update a (z, i) s) T ξ x ^ (n + 1)) D t ∧
          |D| ≤ C * (|phiT a T ξ x| ^ n * (|grad (phiT a T ξ) z i| + 1)
                * |greenT a T (z + unit i) x - greenT a T z x|
              + (|grad (phiT a T ξ) z i| + 1) ^ (n + 1)
                * |greenT a T (z + unit i) x - greenT a T z x| ^ (n + 1))) ∧
    (∃ C : ℝ, ∀ a : Edge d → ℝ, InA α β a → ∀ T : ℝ, 0 < T →
      ∀ ξ : Fin d → ℝ, sqNorm ξ = 1 → ∀ (z : Site d) (i : Fin d), ∀ t ∈ Set.Icc α β,
        |grad (phiT (Function.update a (z, i) t) T ξ) z i|
          ≤ C * (|grad (phiT a T ξ) z i| + 1)) := by sorry

end GloriaOtto.Variance
