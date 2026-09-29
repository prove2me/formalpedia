-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
-- name    : LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/45b81e82-d6cf-5c28-94f3-72615712b8ef
-- title:
--   The standard character of ℚₚ has level 0
-- statement:
--   Let $v$ be a point of the height-one spectrum of the ring of integers of $\mathbb{Q}$, i.e. a finite place of $\mathbb{Q}$, and let $\mathbb{Q}_v$ denote the $v$-adic completion of $\mathbb{Q}$. Write $\psi_{\mathbb{Q},v} =$ `psiLocal ℚ v` for the additive character of $\mathbb{Q}_v$ with values in $\mathbb{C}$ obtained by composing the standard adelic character `stdAddChar ℚ`, namely the character $\psi_K$ attached to the adelic trace data of $\mathbb{Q}$, with the additive map `adeleSingleAt`, which sends $x \in \mathbb{Q}_v$ to the finite adele having component $x$ at $v$ and $0$ elsewhere and then embeds the finite adeles into the full adele ring. For an additive character $\psi$ of $\mathbb{Q}_v$, `addCharLevel` $\psi$ is defined as the supremum in $\mathbb{Z}$ of the set of integers $n$ such that $\psi(x) = 1$ for all $x$ with $\mathrm{v}(x) \le \exp(n)$, i.e. for all $x$ in the fractional ideal $\mathfrak{p}_v^{-n}$. The assertion is that this level is $0$ for $\psi_{\mathbb{Q},v}$, at every finite place $v$.
--
--   This is the statement that the conductor of the standard additive character of $\mathbb{Q}_p$ is $\mathbb{Z}_p$: the character is trivial on the ring of integers and nontrivial on $p^{-1}\mathbb{Z}_p$. It is the normalisation input for the local theory at finite places, used wherever a local functional equation, Whittaker model or root number is computed with respect to a character of level one at the relevant place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.StandardAddChar IsDedekindDomain

theorem LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat
    (v : HeightOneSpectrum (RingOfIntegers ℚ)) :
    addCharLevel (psiLocal ℚ v) = 0 := by sorry
