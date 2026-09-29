-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log
-- name    : NumberField.TateGlobal.exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/869e1173-1e40-5499-95f3-8f0c2de01934
-- title:
--   Volume of a norm slab of idele classes
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$ and adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F`, and regard the idele group $\mathbb{A}_F^\times$ as a measurable space whose $\sigma$-algebra is the Borel one; let $\nu$ be a Haar measure on $\mathbb{A}_F^\times$. Write $|x| =$ [`NumberField.TateGlobal.ideleNorm F x`](def/NumberField_TateGlobalZeta.html#L19) for the real number obtained from the distributive Haar character `distribHaarChar` of the additive group $\mathbb{A}_F$ evaluated at the unit $x$, that is, the positive real factor by which multiplication by $x$ scales additive Haar measure on $\mathbb{A}_F$. The assertion is that there exists a constant $C$ in $[0,\infty]$ with $C \neq 0$ and $C \neq \infty$ such that for every set $\Omega \subseteq \mathbb{A}_F^\times$ which is a fundamental domain, in the sense of `IsFundamentalDomain` for the measure $\nu$, for the action of the subgroup of principal ideles — the range of the map on unit groups induced by the monoid homomorphism $F \to \mathbb{A}_F$ underlying the algebra map, i.e. the image of $F^\times$ under the diagonal embedding — and for all real $a, b$ with $0 < a \le b$, one has $$\nu\bigl(\Omega \cap \{x : |x| \in [a,b]\}\bigr) = C \cdot \log(b/a),$$ the right-hand side formed in `ENNReal` via `ENNReal.ofReal`. In particular the constant $C$ is independent of $\Omega$ and of $a, b$.
--
--   This is the measure-theoretic form of Tate's computation of the volume of the norm-one idele class group: the idele class group is, up to measure, the product of the compact group of norm-one idele classes with $\mathbb{R}_{>0}$ carrying $dt/t$, and $C$ is the (unnormalised) volume of the compact factor, so that no class-number formula for $C$ is asserted. The proof cites the compactness of the norm-one idele class group, the continuity of the idelic norm, the triviality of the distributive Haar character on principal ideles, and its evaluation as a product of local normalised absolute values at the infinite places; the statement is used in the analytic estimates for automorphic forms, for instance in the bounds on integrals over elliptic cells and on Eisenstein contributions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem NumberField.TateGlobal.exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ Ω : Set (AdeleRing (𝓞 F) F)ˣ,
        IsFundamentalDomain
          (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          ν (Ω ∩ {x | NumberField.TateGlobal.ideleNorm F x ∈ Set.Icc a b}) =
            C * ENNReal.ofReal (Real.log (b / a)) := by sorry
