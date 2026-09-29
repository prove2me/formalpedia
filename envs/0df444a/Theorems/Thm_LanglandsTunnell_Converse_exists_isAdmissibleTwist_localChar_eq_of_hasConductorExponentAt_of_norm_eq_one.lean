-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_isAdmissibleTwist_localChar_eq_of_hasConductorExponentAt_of_norm_eq_one
-- name    : LanglandsTunnell.Converse.exists_isAdmissibleTwist_localChar_eq_of_hasConductorExponentAt_of_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/83970863-4263-5e02-a735-46bd2b293b74
-- title:
--   Unitary local character at p extends to an idele class character
-- statement:
--   Let $p$ be a nonzero prime ideal of the ring of integers of $\mathbb{Q}$, let $\omega$ be a homomorphism of groups from the units of the $p$-adic completion of $\mathbb{Q}$ to $\mathbb{C}^\times$, and let $c$ be a natural number such that `HasConductorExponentAt ℚ p ω c` holds: $\omega$ is trivial on the set of units $u$ with $|u| = 1$ and, when $c \neq 0$, $|u - 1| \le \exp(-c)$, while for every $m < c$ there is a unit $u$ with $|u| = 1$ and ($m = 0$ or $|u - 1| \le \exp(-m)$) for which $\omega(u) \neq 1$; assume moreover that $\|\omega(z)\| = 1$ for every unit $z$ of the completion. The conclusion is that there exists a homomorphism $\eta$ from the group of units of the adele ring of $\mathbb{Q}$ to $\mathbb{C}^\times$ which is an admissible twist, i.e. $\eta(u) = 1$ for every $u \in \mathbb{Q}^\times$ embedded in the ideles through the structure map, $\eta$ is continuous, and $\|\eta(x)\| = 1$ for all ideles $x$, and whose local component at $p$ is $\omega$: the composite of $\eta$ with the map sending a unit $t$ of the $p$-adic completion to the idele with infinite component $1$, component $t$ at $p$ and component $1$ at every other finite place, equals $\omega$ as a homomorphism of groups.
--
--   This is the standard existence statement, for the field $\mathbb{Q}$, of a unitary Hecke character with prescribed local component at a single finite place, obtained from the decomposition of the idele class group of $\mathbb{Q}$ as $\mathbb{R}_{>0} \times \prod_\ell \mathbb{Z}_\ell^\times$ together with the openness of the higher unit group on which $\omega$ is trivial. It supplies the global twisting characters used in the Rankin–Selberg local constant computation of the Langlands–Tunnell converse argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_isAdmissibleTwist_localChar_eq_of_hasConductorExponentAt_of_norm_eq_one.lean

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain LanglandsTunnell.Converse
  LanglandsTunnell.TateLocal

theorem LanglandsTunnell.Converse.exists_isAdmissibleTwist_localChar_eq_of_hasConductorExponentAt_of_norm_eq_one
    (p : HeightOneSpectrum (𝓞 ℚ)) (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ)
    (hc : HasConductorExponentAt ℚ p ω c)
    (hu : ∀ z : (p.adicCompletion ℚ)ˣ, ‖((ω z : ℂˣ) : ℂ)‖ = 1) :
    ∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧ localChar η p = ω := by sorry
