-- Prove2me | Theorems.Thm_ModularCurve_exists_conj_mem_GammaH_div
-- name    : ModularCurve.exists_conj_mem_GammaH_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/c5f290d9-37c3-50a7-9868-6f07375a2a67
-- title:
--   Degeneracy conjugation: (a,pb;c/p,d)∈Γ_{H'}(M/p)
-- statement:
--   Let $p$ be a prime, $M$ a nonzero natural number with $p \mid M$, and $H$ a subgroup of $(\mathbb{Z}/M)^\times$. The group [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) is the image in $\mathrm{SL}_2(\mathbb{Z})$ of the subgroup of $\Gamma_0(M)$ consisting of those matrices whose lower-right entry, viewed as a unit of $\mathbb{Z}/M$ via [`CohCarrier.gamma0Units`](def/CohCarrier_Level.html#L121) (whose inverse is the class of the upper-left entry), lies in $H$; and `infSubgroup p M H hpM` is the image of $H$ under the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ coming from $M/p \mid M$. The assertion is that for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), writing $\gamma = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$, there exists $\gamma_1$ in [`CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)`](def/CohCarrier_Level.html#L133) whose entries satisfy $(\gamma_1)_{00} = a$, $(\gamma_1)_{01} = p\,b$, $p\,(\gamma_1)_{10} = c$ and $(\gamma_1)_{11} = d$; that is, $\gamma_1 = \begin{pmatrix} a & pb \\ c/p & d\end{pmatrix}$, the division by $p$ being part of the assertion.
--
--   This is the entry condition for the second degeneracy map at a prime $p$ dividing the level: conjugation by $\mathrm{diag}(p,1)$ carries $\Gamma_H(M)$ into $\Gamma_{H'}(M/p)$, where $H'$ is the image of $H$ modulo $M/p$. It is used by [`ModularCurve.qExpand_mem_xHFunctionField_of_mem_div`](thm.html#ModularCurve.qExpand_mem_xHFunctionField_of_mem_div) in the comparison of $q$-expansions at levels $M$ and $M/p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_conj_mem_GammaH_div.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.exists_conj_mem_GammaH_div
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CohCarrier.GammaH M H) :
    ∃ γ₁ ∈ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM),
      γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (p : ℤ) * γ 0 1 ∧ (p : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by sorry
