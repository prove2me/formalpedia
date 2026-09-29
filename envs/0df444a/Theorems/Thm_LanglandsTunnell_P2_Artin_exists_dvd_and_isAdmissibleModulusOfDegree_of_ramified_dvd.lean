-- Prove2me | Theorems.Thm_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
-- name    : LanglandsTunnell.P2.Artin.exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/8d1aae77-bf8a-57f1-849f-298de967ec5b
-- title:
--   Admissible multiple of a modulus containing the ramification
-- statement:
--   Let $E \subseteq F$ be number fields, $F$ an $E$-algebra, and let $\mathfrak f$ be a nonzero ideal of $\mathcal O_E$ such that for every finite place $v$ of $E$ (a point of the height-one spectrum of $\mathcal O_E$) whose chosen prime `primeAbove E F v` of $\mathcal O_F$ above $v$ has nontrivial inertia subgroup inside $F \simeq_{\mathrm{alg}[E]} F$, the prime $v$ divides $\mathfrak f$. Let $n$ be a natural number. Then there exists an ideal $\mathfrak f'$ of $\mathcal O_E$ with three properties: $\mathfrak f \mid \mathfrak f'$; every prime $v$ dividing $\mathfrak f'$ already divides $\mathfrak f$ (so $\mathfrak f'$ has the same prime support as $\mathfrak f$); and $\mathfrak f'$ is an admissible modulus of degree $n$ for $F/E$, meaning $\mathfrak f' \neq 0$ and for every $v$ whose prime above in $F$ has nontrivial inertia in $F \simeq_{\mathrm{alg}[E]} F$ one has
--   $$v^{\,1 + \sum_{p \mid n} (\mathrm{ord}_p(n)+1)\, e(v \mid p)} \mid \mathfrak f',$$
--   the sum running over the prime factors $p$ of $n$ and $e(v\mid p)$ denoting the ramification index, in the sense of `Ideal.ramificationIdx'`, of $v$ over the ideal $(p)$ of $\mathbb Z$.
--
--   The statement allows one to replace an arbitrary nonzero modulus that is divisible by all primes ramified in $F/E$ by a multiple of it, of the same prime support, at which the degree-$n$ form of the reciprocity law for the Artin symbol is available. It is used in the construction of the Hecke characters and the Frobenius formulae of the Langlands–Tunnell step, where the support of the modulus must not grow.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain HeckeCharacter LanglandsTunnell.P2.Artin

theorem LanglandsTunnell.P2.Artin.exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (𝔣 : Ideal (𝓞 E)) (h𝔣 : 𝔣 ≠ ⊥)
    (hram : ∀ v : HeightOneSpectrum (𝓞 E), (primeAbove E F v).inertia (F ≃ₐ[E] F) ≠ ⊥ → v.asIdeal ∣ 𝔣) (n : ℕ) :
    ∃ 𝔣' : Ideal (𝓞 E), 𝔣 ∣ 𝔣' ∧ (∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔣' → v.asIdeal ∣ 𝔣) ∧
      NumberField.NormIndex.IsAdmissibleModulusOfDegree E F n 𝔣' := by sorry
