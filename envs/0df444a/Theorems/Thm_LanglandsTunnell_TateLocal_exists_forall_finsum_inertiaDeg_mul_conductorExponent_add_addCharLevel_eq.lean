-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq
-- name    : LanglandsTunnell.TateLocal.exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/ad2a0cf9-f1cd-594d-a53d-62abff0f4e56
-- title:
--   Weighted conductor exponents above p sum to 3c
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$ and let $w$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$. The assertion is that there is a natural number $c_0$ with the following property. Let $\chi$ be a monoid homomorphism from the units of the $w$-adic completion $\mathbb{Q}_w$ to $\mathbb{C}^{\times}$, and let $c$ be a natural number with $c_0 \le c$ such that $\chi$ has conductor exponent $c$ at $w$ in the sense of `HasConductorExponentAt`: $\chi$ is trivial on every unit $u$ with $\mathrm{v}(u)=1$ satisfying $c = 0$ or $\mathrm{v}(u-1) \le \exp(-c)$, and for every $m < c$ there is a unit in the corresponding level-$m$ set on which $\chi$ is non-trivial. Let $a$ assign to each prime $P$ of $\mathcal{O}_K$ lying over $w$ (an element of `w.Extension (𝓞 K)`, i.e. a height-one prime $P$ of $\mathcal{O}_K$ whose restriction to $\mathcal{O}_{\mathbb{Q}}$ is $w$) a natural number $a_P$, and suppose that for each such $P$ the character $u \mapsto \chi(N_{K_P/\mathbb{Q}_w}(u))$, obtained by applying $\chi$ to the image of $u$ under the algebra norm relative to $\mathbb{Q}_w$, has conductor exponent $a_P$ at $P$ in the same sense. Then the finite sum $$\sum_{P} f_P\bigl(a_P + \lambda_P\bigr) = 3c,$$ where $f_P$ is the inertia degree `inertiaDeg'` of $w$ in $P$, and $\lambda_P$ is `addCharLevel` of the standard local additive character $\psi_{K,P}$ of $K_P$, namely the supremum of those $n \in \mathbb{Z}$ for which $\psi_{K,P}$ is trivial on all $x$ with $\mathrm{v}(x) \le \exp(n)$, $\psi_{K,P}$ being the standard additive character of the adele ring of $K$ composed with the inclusion of $K_P$ as a single finite component.
--
--   This is the conductor computation underlying the cubic induction: for $\chi$ ramified beyond the three-dimensional representation induced from the trivial character, the conductor exponent of $\chi \otimes \mathrm{Ind}\,1$, expressed through the local norms, the inertia degrees and the levels of the standard additive characters (the local different exponents), equals $3c$. It is used in the `LanglandsTunnell.CubicInduction` results relating the zeta integral of an induced datum to root numbers and to the zeta integral over $\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq
    (K : Type) [Field K] [NumberField K] (hdeg : Module.finrank ℚ K = 3) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ c₀ : ℕ, ∀ (χ : (w.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ), c₀ ≤ c → HasConductorExponentAt ℚ w χ c →
      ∀ a : w.Extension (𝓞 K) → ℕ,
        (∀ P : w.Extension (𝓞 K),
          HasConductorExponentAt K P.1 (χ.comp (Units.map (Algebra.norm (w.adicCompletion ℚ)))) (a P)) →
        ∑ᶠ P : w.Extension (𝓞 K), (w.asIdeal.inertiaDeg' P.1.asIdeal : ℤ) *
            ((a P : ℤ) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K P.1)) =
          3 * c := by sorry
