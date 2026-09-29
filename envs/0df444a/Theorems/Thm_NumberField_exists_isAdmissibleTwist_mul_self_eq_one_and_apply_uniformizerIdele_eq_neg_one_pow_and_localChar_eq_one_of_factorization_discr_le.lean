-- Prove2me | Theorems.Thm_NumberField_exists_isAdmissibleTwist_mul_self_eq_one_and_apply_uniformizerIdele_eq_neg_one_pow_and_localChar_eq_one_of_factorization_discr_le
-- name    : NumberField.exists_isAdmissibleTwist_mul_self_eq_one_and_apply_uniformizerIdele_eq_neg_one_pow_and_localChar_eq_one_of_factorization_discr_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/7bc73899-3992-5336-8504-e5390190b971
-- title:
--   Quadratic sign character with conductor bounded by d_K
-- statement:
--   Let $K$ be a number field. The assertion is that there exists a monoid homomorphism $\omega$ from the ideles $(\mathbb{A}_{\mathbb{Q}})^{\times}$ to $\mathbb{C}^{\times}$ with the following four properties. First, `IsAdmissibleTwist ℚ ω`: $\omega$ kills the principal ideles coming from $\mathbb{Q}^{\times}$, is continuous, and satisfies $|\omega(x)| = 1$ for all $x$. Second, $\omega$ is quadratic: $\omega(x)^2 = 1$ for every idele $x$. Third, for every height one prime $v$ of $\mathbb{Z} = \mathcal{O}_{\mathbb{Q}}$ such that no prime $\mathfrak{P}$ of $\mathcal{O}_K$ lying over $v$ has ramification index $\neq 1$ at $v$: the local component of $\omega$ at $v$ is trivial on all units $t$ of the completion with $t$ and $t^{-1}$ both integral, and $\omega$ evaluated at the idele which is a uniformiser at $v$ and $1$ at all other places (including the infinite ones) equals $(-1)^{[K:\mathbb{Q}] + \#\{\mathfrak{P} : \mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}} = v\}}$. Fourth, a conductor bound: for every $v$ and every $m \geq 1$ such that the exponent of the rational prime $N(v)$ in $|\mathrm{disc}(K)|$ is at most $m$, the local character $\omega_v$ is trivial on the higher unit group at level $m$, namely the units $u$ of the completion with $|u| = 1$ and $|u - 1| \leq q_v^{-m}$.
--
--   This is the quadratic sign character attached to a number field $K$ — classically $\omega = \varepsilon \circ \mathrm{Art}$ for the quadratic field $\mathbb{Q}(\sqrt{d_K})$, whose Frobenius values record the sign of the permutation action on the embeddings of $K$, in the style of Stickelberger's theorem — together with the bound $\mathfrak{f}(\omega) \mid d_K$ expressing that its conductor exponent at each prime is at most the exponent of that prime in the discriminant of $K$. It feeds the cubic-induction step of the Langlands–Tunnell converse argument, where the conductor clause is what controls the twist at the ramified primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_isAdmissibleTwist_mul_self_eq_one_and_apply_uniformizerIdele_eq_neg_one_pow_and_localChar_eq_one_of_factorization_discr_le.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda
  LanglandsTunnell.TateLocal HeckeCharacter

theorem NumberField.exists_isAdmissibleTwist_mul_self_eq_one_and_apply_uniformizerIdele_eq_neg_one_pow_and_localChar_eq_one_of_factorization_discr_le
    (K : Type) [Field K] [NumberField K] :
    ∃ ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ ω ∧ (∀ x, ω x * ω x = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsRamifiedIn K v →
        IsUnramifiedCharAt ω v ∧
          ((ω (uniformizerIdele ℚ v) : ℂˣ) : ℂ) = (-1) ^ (Module.finrank ℚ K + Nat.card (primeFibre ℚ K v))) ∧
      ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (m : ℕ), 1 ≤ m →
        (discr K).natAbs.factorization (Ideal.absNorm v.asIdeal) ≤ m →
          ∀ u ∈ higherUnitsAt ℚ v m, localChar ω v u = 1 := by sorry
