-- Prove2me | Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV
-- name    : NumberField.StandardAddChar.psiLocal_rat_eq_psiV
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/30355549-2f07-50bd-99b8-efed38fc2257
-- title:
--   Local component at v of the standard adelic character of ℚ
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, i.e. a finite place of $\mathbb{Q}$, and let $\mathbb{Q}_v$ denote the $v$-adic completion. The theorem asserts an equality of two additive characters $\mathbb{Q}_v \to \mathbb{C}^\times$. The first, `psiLocal ℚ v`, is the composite of the standard additive character `stdAddChar ℚ` of the adele ring of $\mathbb{Q}$ — by definition the character $\psi_K$ attached to the adelic trace data of $\mathbb{Q}$ — with the additive monoid homomorphism `adeleSingleAt`, which sends $x \in \mathbb{Q}_v$ to the adele whose infinite part is $0$ and whose finite part is the finite adele with component $x$ at $v$ and $0$ at every other finite place. The second, `psiV v`, is the character $x \mapsto \psi_p(\iota_v(x))$, where $\iota_v$ is the isomorphism `adicCompletion.padicEquiv v` of $\mathbb{Q}_v$ with $\mathbb{Q}_p$ for the prime $p$ corresponding to $v$, and $\psi_p$ is the standard additive character `psiPadic` of $\mathbb{Q}_p$, built from the function `psiPadicFun` together with its additivity and normalisation at $0$. The conclusion is the equality of these two characters of $\mathbb{Q}_v$.
--
--   This is the statement, for the base field $\mathbb{Q}$, that the local component at a finite place of the standard additive character of the adeles coincides with the standard character of $\mathbb{Q}_p$; it is the normalisation that makes the local theory at finite places of $\mathbb{Q}$ match the global adelic character used in Tate-style local computations. It is invoked throughout the work on Whittaker models and local level-one computations for automorphic forms on $\mathrm{GL}_2$ over $\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain

theorem NumberField.StandardAddChar.psiLocal_rat_eq_psiV
    (v : HeightOneSpectrum (RingOfIntegers ℚ)) :
    psiLocal ℚ v = psiV v := by sorry
