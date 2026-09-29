-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_hasConductorExponentAt_localChar_comp_genuineBeta_le
-- name    : NumberField.TateGlobal.exists_hasConductorExponentAt_localChar_comp_genuineBeta_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/e0b8fc87-fd61-55a0-8636-107f945a6d0d
-- title:
--   Conductor exponent of an idele character under adelic base change
-- statement:
--   Let $K$ be a number field whose ring of integers is equipped with an integral $\mathcal{O}_{\mathbb{Q}}$-algebra structure, let $\mu : (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ be a group homomorphism from the units of the adele ring of $K$ to $\mathbb{C}^\times$ (no continuity is assumed), let $p$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$ and let $M$ be a natural number. Write $\chi_v$ for the local component `localChar` of a character at a finite place $v$, obtained by composing the character with the map sending $t \in (K_v)^\times$ to the unit of $\mathbb{A}_K$ having $t$ at $v$, $1$ at all other finite places and $1$ at the infinite component; and say that $\chi_v$ has conductor exponent $c$ when $\chi_v$ is trivial on `higherUnitsAt` at level $c$ — the units $u$ of $K_v$ with $|u| = 1$ and, for $c > 0$, $|u - 1| \le \exp(-c)$ — while for each $m < c$ some unit at level $m$ is not killed. Assume that for every height-one prime $w$ of $\mathcal{O}_K$ lying in the fibre `primeFibre` over $p$, i.e. with $w \cap \mathcal{O}_{\mathbb{Q}} = p$, the local component $\mu_w$ has some conductor exponent $a_w \le M$. Then there is $e \le M$ such that the local component at $p$ of the character $\mu \circ (M4aHerbrand.Bridge.genuineβ\ \mathbb{Q}\ K)^\times$, the pullback of $\mu$ along the map induced on units by the adelic base-change homomorphism [`M4aHerbrand.Bridge.genuineβ ℚ K`](def/M4aHerbrand_GenuineBeta.html#L14) from $\mathbb{A}_{\mathbb{Q}}$ to $\mathbb{A}_K$, has conductor exponent $e$.
--
--   This is the standard comparison of conductors of a quasi-character of a local field with those of its components above it in a finite extension: principal units of $\mathbb{Q}_p$ congruent to $1$ modulo $p^M$ land in the $M$-th principal unit group at every prime above $p$. It supplies the conductor bound for the restriction to the ideles of $\mathbb{Q}$ of the central character occurring in the cubic automorphic induction step, and is used by [`LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound`](thm.html#LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_hasConductorExponentAt_localChar_comp_genuineBeta_le.lean

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_M4aHerbrand_GenuineBeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.RankinSelberg

theorem NumberField.TateGlobal.exists_hasConductorExponentAt_localChar_comp_genuineBeta_le
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (p : HeightOneSpectrum (𝓞 ℚ)) (M : ℕ)
    (hμ : ∀ w ∈ primeFibre ℚ K p, ∃ aw : ℕ, aw ≤ M ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt K w (NumberField.TateGlobal.localChar μ w) aw) :
    ∃ e : ℕ, e ≤ M ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p
        (NumberField.TateGlobal.localChar (μ.comp (Units.map (M4aHerbrand.Bridge.genuineβ ℚ K).toMonoidHom)) p) e := by sorry
