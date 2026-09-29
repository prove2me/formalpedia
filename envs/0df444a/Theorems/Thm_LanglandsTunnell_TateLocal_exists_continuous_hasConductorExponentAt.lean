-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt
-- name    : LanglandsTunnell.TateLocal.exists_continuous_hasConductorExponentAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/8e3a676e-16cf-59ac-8637-13e99c8c60c9
-- title:
--   Existence of characters with prescribed exact conductor exponent
-- statement:
--   Let $K$ be a number field, let $v$ be a nonzero prime of its ring of integers $\mathcal{O}_K$ (a point of the height-one spectrum), and let $c$ be a natural number with $c \ge 2$. Write $K_v$ for the $v$-adic completion of $K$, equipped with its valuation $\mathrm{Valued.v}$ taking values in a multiplicatively written value group. For a natural number $n$, let $U^{(n)}$ denote the set of units $u \in K_v^{\times}$ such that $\mathrm{Valued.v}(u) = 1$ and, in case $n \neq 0$, also $\mathrm{Valued.v}(u - 1) \le \exp(-n)$; thus $U^{(0)}$ is the unit group of the valuation ring and $U^{(n)}$ for $n \ge 1$ is the group of units congruent to $1$ to level $n$. Let $\varpi_v \in K_v^{\times}$ be the unit attached to the chosen uniformizer of the $v$-adic integral valuation in $\mathcal{O}_K$, viewed in $K_v$. The assertion is that there exists a group homomorphism $\chi \colon K_v^{\times} \to \mathbb{C}^{\times}$ which is continuous, satisfies $\chi(\varpi_v) = 1$, is trivial on all of $U^{(c)}$, and is such that for every $m < c$ there is some $u \in U^{(m)}$ with $\chi(u) \neq 1$; that is, $\chi$ has conductor exponent exactly $c$ in the sense of the predicate `HasConductorExponentAt`.
--
--   This is the local existence statement for multiplicative characters of a nonarchimedean local field with prescribed exact conductor exponent, normalised so as to be trivial on the fixed uniformizer. It feeds the construction of local characters and root numbers in the Tate local-constants part of the Langlands–Tunnell argument, being used by [`LanglandsTunnell.TateLocal.exists_continuous_hasConductorExponentAt_apply_ne`](thm.html#LanglandsTunnell.TateLocal.exists_continuous_hasConductorExponentAt_apply_ne) and by the cubic-induction step [`LanglandsTunnell.CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated`](thm.html#LanglandsTunnell.CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated). The restriction $c \ge 2$ is genuine: for $c = 1$ one would need a nontrivial character of the residue field's multiplicative group, which fails when the residue field has two elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt.lean

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem LanglandsTunnell.TateLocal.exists_continuous_hasConductorExponentAt
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (c : ℕ) (hc : 2 ≤ c) :
    ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ,
      Continuous χ ∧ χ (uniformizerUnit K v) = 1 ∧ HasConductorExponentAt K v χ c := by sorry
