-- Prove2me | Theorems.Thm_GenCountSampleLLL_lemma_3_4
-- name    : GenCountSampleLLL.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:52:56.218024+00:00
-- url     : https://prove2.me/theorems/b97a7353-c602-4673-9f74-8c7e2ac0793a
-- title:
--   Lemma 3.4, p.15 — $\mathbb EA\le\mathbb EA^2\le2cx_a$, $\sum_{\mathcal T}\prod\rho_t\le4cx_a$, $\sum_{\mathcal T}\ell_x(\mathcal T)\prod\rho_t<10cx_a$
-- statement:
--   Assume (1.1) with $c=1/100$ for some $x\in(0,1)^{\mathcal C}$ and let $a\in\mathcal D\subseteq\mathcal C$. Let $A$ be the number of sets $\mathcal B\subseteq\mathcal D$ of active constraints with $a\in\mathcal B$ and $G^2_{\mathcal D}[\mathcal B]$ connected, where each $b\in\mathcal D$ is active when its independent local sample $\sigma_b\sim\nu_{\mathrm{vbl}(b)}$ violates $b$. Then $\mathbb EA\le\mathbb EA^2\le2c\,x_a$, and
--   $$
--   \sum_{\mathcal T\in\mathfrak T_{\mathcal D,a}}\prod_{t\in\mathcal T}\rho_t\le4c\,x_a,\qquad\sum_{\mathcal T\in\mathfrak T_{\mathcal D,a}}\ell_x(\mathcal T)\prod_{t\in\mathcal T}\rho_t<10c\,x_a.\tag{3.3}
--   $$
--
--   These sums bound the running time of the estimator, the number of recursive calls, and the mass and flow estimates of the sampler.
--
--   Differences from the source:
--   - encoding: the standing assumption of §2, p.7: "Throughout the proof, we assume (1.1) with c = 1/100", with x ∈ (0,1)^𝒞 → explicit hypotheses `hx : ∀ b, 0 < x b ∧ x b < 1` and `hLLL : I.LLLCond (1/100) x`; reason: the statement on the page omits the section's standing assumption; the Lean states it
--   - encoding: "the number A of active connected sets containing a in G²_𝒟" and its expectations → `numConn D a (active D ω)` under the law of the list experiment, with expectations as finite sums; reason: "active" is the paper's (p.11)
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), Lemma 3.4, (3.3), p.15

import Mathlib
import Definitions.Def_GenCountSampleLLL_Inst
import Definitions.Def_GenCountSampleLLL_twoTrees

set_option autoImplicit false

open scoped BigOperators ENNReal

open Classical

namespace GenCountSampleLLL

open Inst

/-- Lemma 3.4, p.15 (Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671 (held file sha256 cd449f83…)), under (1.1) with `c = 1/100`. For every `a ∈ D ⊆ C`,
the number `A` of active connected sets containing `a` in `G²_D` satisfies `EA ≤ EA² ≤ 2c x_a`;
moreover `Σ_{T ∈ T_{D,a}} ∏_{t ∈ T} ρ_t ≤ 4c x_a` and
`Σ_{T ∈ T_{D,a}} ℓ_x(T) ∏_{t ∈ T} ρ_t < 10c x_a` (3.3).

**Formalization Note.** "Active" is that of the list experiment (p.11): `b ∈ D` is active when
its independent local draw `σ_b ∼ ν_{vbl(b)}` violates `b`. `A` counts the sets `B ⊆ D` of active
constraints with `a ∈ B` and `G²_D[B]` connected, and the expectations are finite sums against
the experiment's law. -/
theorem lemma_3_4 (I : Inst) (x : Fin I.m → ℝ) (hx : ∀ b, 0 < x b ∧ x b < 1)
    (hLLL : I.LLLCond (1 / 100) x) (D : Finset (Fin I.m)) (a : Fin I.m) (ha : a ∈ D) :
    (∑ ω, (I.expLaw ω).toReal * (I.numConn D a (I.active D ω) : ℝ)) ≤
        ∑ ω, (I.expLaw ω).toReal * (I.numConn D a (I.active D ω) : ℝ) ^ 2 ∧
      (∑ ω, (I.expLaw ω).toReal * (I.numConn D a (I.active D ω) : ℝ) ^ 2) ≤
        2 * (1 / 100) * x a ∧
      ∑ T ∈ I.twoTrees D a, ∏ t ∈ T, I.rho (1 / 100) x t ≤ 4 * (1 / 100) * x a ∧
      ∑ T ∈ I.twoTrees D a, I.ellx x D a T * ∏ t ∈ T, I.rho (1 / 100) x t <
        10 * (1 / 100) * x a := by sorry

end GenCountSampleLLL
