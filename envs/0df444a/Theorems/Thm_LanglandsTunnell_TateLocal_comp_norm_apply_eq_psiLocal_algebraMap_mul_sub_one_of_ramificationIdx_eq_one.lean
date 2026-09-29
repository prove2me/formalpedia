-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_comp_norm_apply_eq_psiLocal_algebraMap_mul_sub_one_of_ramificationIdx_eq_one
-- name    : LanglandsTunnell.TateLocal.comp_norm_apply_eq_psiLocal_algebraMap_mul_sub_one_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/5d24c6b3-9361-50e4-888c-25a68ae95c9a
-- title:
--   Transport of a character's local pin along the norm, e=1
-- statement:
--   Let $K$ be a number field, $v$ a height-one prime of $\mathcal{O}_{\mathbb{Q}}$ and $w$ an extension of $v$ to $\mathcal{O}_K$, i.e. a height-one prime $w.1$ of $\mathcal{O}_K$ lying under $v$, and assume the ramification index $e(v.\mathrm{asIdeal}, w.1.\mathrm{asIdeal})$ equals $1$. Let $\chi$ be a multiplicative homomorphism from the units of the $v$-adic completion $\mathbb{Q}_v$ to $\mathbb{C}^\times$ which has conductor exponent $a \in \mathbb{N}$ at $v$, meaning that $\chi$ is trivial on $\mathrm{higherUnitsAt}\ \mathbb{Q}\ v\ a$ — the set of units $u$ with $|u| = 1$ and, when $a \neq 0$, $|u - 1| \le \exp(-a)$ — while for every $m < a$ some element of $\mathrm{higherUnitsAt}\ \mathbb{Q}\ v\ m$ is not killed by $\chi$. Let $c \in \mathbb{Q}_v^\times$ be such that, for every unit $u$ in $\mathrm{higherUnitsAt}\ \mathbb{Q}\ v\ ((a-1)/2+1)$ (truncated subtraction and natural division), $\chi(u) = \psi_{\mathbb{Q},v}(c\,(u-1))$, where $\psi_{\mathbb{Q},v}$ is the local additive character obtained by composing the standard adelic character with the inclusion of $\mathbb{Q}_v$ as the $v$-component of the adele ring. The conclusion is that for every unit $u$ of $K_{w.1}$ in $\mathrm{higherUnitsAt}\ K\ w.1\ ((a-1)/2+1)$, the character $\chi$ composed with the local norm map $K_{w.1}^\times \to \mathbb{Q}_v^\times$ takes at $u$ the value $\psi_{K,w.1}\big(c\,(u-1)\big)$, with $c$ transported by the structure map $\mathbb{Q}_v \to K_{w.1}$.
--
--   This is the statement that an explicit additive "pin" $\chi(u) = \psi(c(u-1))$ for a character of a deep level at $v$ persists, with the same constant $c$ and the same level, after composition with the local norm from an extension in which $v$ is unramified; the standard local character of $K_{w.1}$ is the standard character of $\mathbb{Q}_v$ composed with the local trace, as recorded in [`NumberField.StandardAddChar.psiLocal_eq_psiLocal_trace`](thm.html#NumberField.StandardAddChar.psiLocal_eq_psiLocal_trace). It is used in the cubic-induction arguments of the Langlands–Tunnell input, where local root numbers and functional equations of induced characters are compared.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_comp_norm_apply_eq_psiLocal_algebraMap_mul_sub_one_of_ramificationIdx_eq_one.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.comp_norm_apply_eq_psiLocal_algebraMap_mul_sub_one_of_ramificationIdx_eq_one
    (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 ℚ)) (w : v.Extension (𝓞 K))
    (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ) (hχ : HasConductorExponentAt ℚ v χ a)
    (c : (v.adicCompletion ℚ)ˣ)
    (hc : ∀ u ∈ higherUnitsAt ℚ v ((a - 1) / 2 + 1),
      (χ u : ℂ) =
        NumberField.StandardAddChar.psiLocal ℚ v ((c : v.adicCompletion ℚ) * ((u : v.adicCompletion ℚ) - 1))) :
    ∀ u ∈ higherUnitsAt K w.1 ((a - 1) / 2 + 1),
      ((χ.comp (Units.map (Algebra.norm (v.adicCompletion ℚ)))) u : ℂ) =
        NumberField.StandardAddChar.psiLocal K w.1
          (algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K) (c : v.adicCompletion ℚ) *
            ((u : w.1.adicCompletion K) - 1)) := by sorry
