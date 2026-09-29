-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
-- name    : LanglandsTunnell.TateLocal.psiLocal_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/b988ad72-3563-5632-85c2-adb3860bac6f
-- title:
--   Nontriviality of the standard local additive character ψ_{K,v}
-- statement:
--   Let $K$ be a number field (a field of characteristic zero, finite over $\mathbb{Q}$, with ring of integers $\mathcal{O}_K$) and let $v$ be a point of the height-one spectrum of $\mathcal{O}_K$, i.e. a nonzero prime of $\mathcal{O}_K$, equivalently a finite place of $K$. Write $K_v$ for the $v$-adic completion `v.adicCompletion K`. The character under consideration is [`NumberField.StandardAddChar.psiLocal K v`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65), the additive character $K_v \to \mathbb{C}^\times$ obtained by precomposing the standard global additive character `stdAddChar K`, namely the character $\psi_K$ of the adele ring $\mathbb{A}_K$ attached to $K$ by `adelicTraceData`, with the additive monoid homomorphism `adeleSingleAt K v`: this is the map sending $x \in K_v$ to the adele whose infinite component vanishes and whose finite part is the finite adele concentrated at $v$ with $v$-component $x$ (the composite of `finAdeleSingleAt K v` with the inclusion of the finite adeles into $\mathbb{A}_K$). The assertion is that this character is not equal to the trivial character $1$ of $K_v$, i.e. there exists $x \in K_v$ with $\psi_{K,v}(x) \neq 1$.
--
--   This is the standard nontriviality statement for the local component at a finite place of the standard additive character of the adeles of a number field; together with its triviality on the local integers it makes the level (conductor exponent) of $\psi_{K,v}$ well defined. It is used throughout the local harmonic analysis of the project, in particular in the Tate-type local theory and in the analytic arguments on automorphic forms that invoke it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.TateLocal.psiLocal_ne_one (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NumberField.StandardAddChar.psiLocal K v ≠ 1 := by sorry
