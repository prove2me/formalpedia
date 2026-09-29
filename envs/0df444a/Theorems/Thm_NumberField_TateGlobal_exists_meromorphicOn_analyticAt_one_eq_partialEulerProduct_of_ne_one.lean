-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_meromorphicOn_analyticAt_one_eq_partialEulerProduct_of_ne_one
-- name    : NumberField.TateGlobal.exists_meromorphicOn_analyticAt_one_eq_partialEulerProduct_of_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/04e36cf6-0a37-5261-92e0-fb5c445590ae
-- title:
--   Holomorphy at s=1 of a nontrivial Hecke L-function
-- statement:
--   Let $F$ be a number field, $S$ a finite set of height-one primes of $\mathcal{O}_F$ (finite places of $F$), and let $\varpi$ assign to each finite place $v$ a unit $\varpi_v$ of the completion $F_v$ whose normalised valuation is $\mathrm{ofAdd}(-1)$, i.e. a uniformiser. Let $\chi\colon (\mathbb{A}_F)^\times \to \mathbb{C}^\times$ be a continuous group homomorphism on the ideles which is unitary, in the sense that $\lVert\chi(x)\rVert = 1$ for every idele unit $x$, and which is an idele class character, in the sense that $\chi$ kills the principal ideles: $\chi(\mathrm{algebraMap}\,(u)) = 1$ for every $u \in F^\times$; assume moreover $\chi \neq 1$. Then there exists $L\colon \mathbb{C}\to\mathbb{C}$ which is meromorphic on all of $\mathbb{C}$, is analytic at the point $1$, and satisfies, for every $s$ with $\operatorname{Re} s > 1$,
--   $$L(s) = \Bigl(\prod_{v \notin S}' \bigl(1 - \chi_v(\varpi_v)\,N(v)^{-s}\bigr)\Bigr)^{-1},$$
--   the unrestricted infinite product being taken over the subtype of places not in $S$ and the inverse being taken of the product itself rather than factorwise. Here $N(v) =$ `Ideal.absNorm` of the prime of $\mathcal{O}_F$ underlying $v$, and $\chi_v$ is `localChar`: the composite of $\chi$ with the map sending $t \in F_v^\times$ to the idele whose infinite component is $1$ and whose finite component is $t$ at $v$ and $1$ at every other finite place.
--
--   This is the analytic continuation of the partial Hecke $L$-function attached to a unitary idele class character, as in Tate's thesis, together with the classical absence of a pole at $s=1$ for a nontrivial character (for $\chi = 1$ the product is a partial Dedekind zeta function and has a simple pole there). It is used in the project to produce nonvanishing limits along punctured neighbourhoods of $s=1$ and, through that, in the cuspidality criterion for the forms arising from cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_meromorphicOn_analyticAt_one_eq_partialEulerProduct_of_ne_one.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain

theorem NumberField.TateGlobal.exists_meromorphicOn_analyticAt_one_eq_partialEulerProduct_of_ne_one
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχF : IsIdeleClassChar (𝓞 F) F χ) (hχ1 : χ ≠ 1) :
    ∃ L : ℂ → ℂ, MeromorphicOn L Set.univ ∧
      (∀ s : ℂ, 1 < s.re →
        L s = (∏' v : {v // v ∉ S},
          (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) ∧
      AnalyticAt ℂ L 1 := by sorry
