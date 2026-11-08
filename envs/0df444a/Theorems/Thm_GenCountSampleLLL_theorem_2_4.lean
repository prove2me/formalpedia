-- Prove2me | Theorems.Thm_GenCountSampleLLL_theorem_2_4
-- name    : GenCountSampleLLL.theorem_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:54:00.020503+00:00
-- url     : https://prove2.me/theorems/331bd7ef-47ad-4253-a431-1dfe07c8a1d9
-- title:
--   Theorem 2.4, p.9 — $\mathbf 1_{B_a}\mathbf 1_{\mathrm{Good}(\mathcal D^-)}=\sum_{\mathcal T}(-1)^{|\mathcal T|-1}\mathbf 1_{E_{\mathcal T}}\mathbf 1_{\mathrm{Good}(\mathcal D_{\mathcal T})}$
-- statement:
--   For every $a\in\mathcal D\subseteq\mathcal C$ and every assignment $\sigma\in\Omega$,
--   $$
--   \mathbf 1_{B_a}(\sigma)\,\mathbf 1_{\mathrm{Good}(\mathcal D^-)}(\sigma)=\sum_{\mathcal T\in\mathfrak T_{\mathcal D,a}}(-1)^{|\mathcal T|-1}\,\mathbf 1_{E_{\mathcal T}}(\sigma)\,\mathbf 1_{\mathrm{Good}(\mathcal D_{\mathcal T})}(\sigma).\tag{2.2}
--   $$
--
--   Taking expectations gives the 2-tree expansion of $r_{\mathcal D,a}$, and the same identity drives the recursion for $\mu_{\mathcal D^-}-\mu_{\mathcal D}$.
--
--   Differences from the source:
--   - generalization: stated under the standing assumption (1.1) with c = 1/100 (§2, p.7) → stated for every instance, without (1.1); reason: the statement is combinatorial and does not use (1.1); adding the hypothesis gives the source's statement
--   - encoding: an identity of indicator functions, pointwise on Ω → an equality of integers at every assignment σ; reason: the same statement
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), Theorem 2.4, (2.2), p.9

import Mathlib
import Definitions.Def_GenCountSampleLLL_Inst
import Definitions.Def_GenCountSampleLLL_twoTrees

set_option autoImplicit false

open scoped BigOperators ENNReal

open Classical

namespace GenCountSampleLLL

open Inst

/-- Theorem 2.4, p.9 (Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671 (held file sha256 cd449f83…)). For every `a ∈ D ⊆ C`, pointwise on `Ω`,
`1_{B_a} 1_{Good(D⁻)} = Σ_{T ∈ T_{D,a}} (−1)^{|T|−1} 1_{E_T} 1_{Good(D_T)}` (2.2).

**Formalization Note.** An identity of integers at every assignment `σ`; it holds for every
instance, so (1.1) is not assumed. -/
theorem theorem_2_4 (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m) (ha : a ∈ D)
    (σ : I.Assign) :
    (if I.bad a σ then (1 : ℤ) else 0) * (if σ ∈ I.Good (D.erase a) then 1 else 0) =
      ∑ T ∈ I.twoTrees D a, (-1 : ℤ) ^ (T.card - 1) * (if I.inET D a T σ then 1 else 0) *
        (if σ ∈ I.Good (I.DT D T) then 1 else 0) := by sorry

end GenCountSampleLLL
