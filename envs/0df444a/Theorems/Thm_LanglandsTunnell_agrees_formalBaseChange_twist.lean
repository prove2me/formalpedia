-- Prove2me | Theorems.Thm_LanglandsTunnell_agrees_formalBaseChange_twist
-- name    : LanglandsTunnell.agrees_formalBaseChange_twist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/406fe54c-edfe-5462-9a36-3c96a21bdf42
-- title:
--   Formal base change commutes with twisting
-- statement:
--   Let $F$ and $K$ be number fields, with $\mathcal{O}_K$ given as an $\mathcal{O}_F$-algebra that is integral over $\mathcal{O}_F$, and let $R$ be a commutative ring. Let $\pi$ be a Hecke eigensystem over $F$ with values in $R$, that is, a nonzero level ideal of $\mathcal{O}_F$ together with two tables $a_\pi, b_\pi$ on the height-one primes of $\mathcal{O}_F$, and let $\chi$ be an arbitrary function from the height-one primes of $\mathcal{O}_F$ to $R$. Here the twist $\pi.\mathrm{twist}\,\chi$ keeps the level and has tables $(\chi\,a_\pi, \chi^2 b_\pi)$; the formal base change of an eigensystem has level $\top$ and, at a prime $\mathfrak{P}$ of $\mathcal{O}_K$ with underlying prime $\mathfrak{p}$ of $\mathcal{O}_F$ and inertia degree $f = \mathrm{inertiaDeg}'(\mathfrak{p},\mathfrak{P})$, tables $\mathrm{satakePow}_f(a_\pi(\mathfrak{p}), b_\pi(\mathfrak{p}))$ and $b_\pi(\mathfrak{p})^f$, where $\mathrm{satakePow}$ is the power-sum recursion $p_0 = 2$, $p_1 = s$, $p_{n+2} = s\,p_{n+1} - e\,p_n$; and $\mathrm{bcWeight}\,\chi$ sends $\mathfrak{P}$ to $\chi(\mathfrak{p})^f$. The assertion is that the base change of $\pi.\mathrm{twist}\,\chi$ and the twist of the base change of $\pi$ by $\mathrm{bcWeight}\,\chi$ agree away from a finite set: there is a finite set $S$ of height-one primes of $\mathcal{O}_K$ such that outside $S$ both $a$-tables and both $b$-tables coincide. Note that only the tables are compared, not the levels.
--
--   This is the formal (Satake-parameter) shadow of the compatibility of base change for $\mathrm{GL}_2$ with twisting by a character: the lift of $\pi\otimes\chi$ is the lift of $\pi$ twisted by $\chi\circ N_{K/F}$. It is used in [`LanglandsTunnell.formalBaseChange_twist_rpow_absNorm_agreesAwayFromFinite`](thm.html#LanglandsTunnell.formalBaseChange_twist_rpow_absNorm_agreesAwayFromFinite), where the twist is by a power of the absolute norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_agrees_formalBaseChange_twist.lean

import Definitions.Def_LanglandsTunnell_BcWeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem LanglandsTunnell.agrees_formalBaseChange_twist
    (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra (𝓞 F) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 F) (𝓞 K)] {R : Type*} [CommRing R] (π : HeckeEigensystem F R)
    (χ : HeightOneSpectrum (𝓞 F) → R) :
    (formalBaseChange F K (π.twist χ)).AgreesAwayFromFinite ((formalBaseChange F K π).twist
      (LanglandsTunnell.bcWeight F K χ)) := by sorry
