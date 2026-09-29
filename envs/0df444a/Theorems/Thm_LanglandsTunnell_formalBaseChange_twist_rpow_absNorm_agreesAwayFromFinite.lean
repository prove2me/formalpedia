-- Prove2me | Theorems.Thm_LanglandsTunnell_formalBaseChange_twist_rpow_absNorm_agreesAwayFromFinite
-- name    : LanglandsTunnell.formalBaseChange_twist_rpow_absNorm_agreesAwayFromFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/ac5b52b5-8254-59ff-9188-448c1bbb51a1
-- title:
--   Formal base change commutes with norm twists
-- statement:
--   Let $F$ and $K$ be number fields, equipped with an algebra structure of $\mathcal{O}_F$ on $\mathcal{O}_K$ that is integral, let $\Phi$ be a Hecke eigensystem for $F$ with values in $\mathbb{C}$ — that is, a nonzero level ideal of $\mathcal{O}_F$ together with two functions $a,b$ from the height-one primes of $\mathcal{O}_F$ to $\mathbb{C}$ — and let $t \in \mathbb{R}$. Write $\chi_F(v) = (\mathrm{absNorm}\, v)^{-t}$ and $\chi_K(\mathfrak{P}) = (\mathrm{absNorm}\, \mathfrak{P})^{-t}$, real powers of the absolute ideal norms viewed in $\mathbb{C}$. Twisting an eigensystem by a character multiplies $a$ by the character and $b$ by its square, leaving the level unchanged; the formal base change `formalBaseChange` of an eigensystem has level $\top$, and at a prime $\mathfrak{P}$ of $\mathcal{O}_K$ lying under the prime $\mathfrak{p}$ of $\mathcal{O}_F$ with residue degree $f = \mathrm{inertiaDeg}'$, its $a$-value is `satakePow` $f$ applied to $(a(\mathfrak{p}), b(\mathfrak{p}))$ and its $b$-value is $b(\mathfrak{p})^f$. The assertion is that the formal base change of $\Phi \otimes \chi_F$ and the twist by $\chi_K$ of the formal base change of $\Phi$ agree away from finitely many primes: there is a finite set $S$ of height-one primes of $\mathcal{O}_K$ such that for every $\mathfrak{P} \notin S$ both the $a$-values and the $b$-values of the two eigensystems coincide.
--
--   This is the compatibility of formal base change with unitary (norm-power) normalisation of a Hecke eigensystem, the shape needed when passing between arithmetic and unitary normalisations over $F$ and over $K$. It feeds into the archimedean compatibility step of cubic base change in the Langlands–Tunnell part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_formalBaseChange_twist_rpow_absNorm_agreesAwayFromFinite.lean

import Definitions.Def_AutomorphicForm_FormalBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.formalBaseChange_twist_rpow_absNorm_agreesAwayFromFinite
    (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
    (Φ : HeckeEigensystem F ℂ) (t : ℝ) :
    (formalBaseChange F K (Φ.twist (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)))).AgreesAwayFromFinite
      ((formalBaseChange F K Φ).twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))) := by sorry
