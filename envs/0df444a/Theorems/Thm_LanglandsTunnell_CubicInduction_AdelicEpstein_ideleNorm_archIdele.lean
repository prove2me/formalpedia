-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_ideleNorm_archIdele
-- name    : LanglandsTunnell.CubicInduction.AdelicEpstein.ideleNorm_archIdele
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/4e9fcfb4-c768-5835-b075-c1ae485a10a6
-- title:
--   Idele norm of a positive archimedean scalar idele
-- statement:
--   Let $s$ be a real number with $0 < s$. Here $\mathbb{A}$ denotes the adele ring of $\mathbb{Q}$, and for a unit $x$ of $\mathbb{A}$ the quantity [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19) $\mathbb{Q}$ $x$ is the module of $x$, namely the nonnegative real scaling factor `distribHaarChar` by which multiplication by $x$ distorts the Haar measure of $\mathbb{A}$, viewed as a real number. The idele $\mathrm{archIdele}\,t$ attached to a real $t$ is defined to be $1$ when $t = 0$, and otherwise to be the image under [`NumberField.TateGlobal.archUnitHom`](def/NumberField_TateGlobalZeta.html#L35) at the unique infinite place of $\mathbb{Q}$ of the unit $\mathrm{ofReal}\,t$ of the completion at that place, where $\mathrm{ofReal}$ is the inverse of the ring isomorphism between that completion and $\mathbb{R}$ coming from the place being real; concretely, `archUnitHom` produces the idele whose infinite-adelic component is $1$ altered at the chosen place to the given value, and whose finite-adelic component is $1$. The assertion is that the idele norm of $\mathrm{archIdele}\,s$ equals $s$.
--
--   This is the computation of Tate's idele-norm (module) character on the one-parameter group of positive archimedean scalars in the adeles of $\mathbb{Q}$, identifying that group as a section of the norm map. It is used in the construction of a fundamental domain for the mirabolic action and the attendant factorisation of integrals against the adelic measure in the Epstein-series part of the cubic-induction argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_ideleNorm_archIdele.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.AdelicEpstein.ideleNorm_archIdele (s : ℝ) (hs : 0 < s) :
    NumberField.TateGlobal.ideleNorm ℚ (archIdele s) = s := by sorry
