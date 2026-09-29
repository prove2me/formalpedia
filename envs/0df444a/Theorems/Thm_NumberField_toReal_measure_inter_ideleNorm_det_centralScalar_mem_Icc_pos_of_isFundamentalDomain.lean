-- Prove2me | Theorems.Thm_NumberField_toReal_measure_inter_ideleNorm_det_centralScalar_mem_Icc_pos_of_isFundamentalDomain
-- name    : NumberField.toReal_measure_inter_ideleNorm_det_centralScalar_mem_Icc_pos_of_isFundamentalDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/5edb0281-16ad-596b-b759-28823df45521
-- title:
--   Positivity of the norm-band constant of a fundamental domain
-- statement:
--   Let $K$ be a number field and let $\alpha,\beta$ be real numbers with $0<\alpha$ and $\alpha<\beta$. Equip the group of units $(\mathbb{A}_K)^\times$ of the adele ring $\mathrm{AdeleRing}(\mathcal{O}_K,K)$ with a measurable structure that is the Borel structure of its topology, let $\nu_{Z_K}$ be a Haar measure on $(\mathbb{A}_K)^\times$, and let $\Omega_K\subseteq(\mathbb{A}_K)^\times$ be a fundamental domain, in the sense of `MeasureTheory.IsFundamentalDomain` for $\nu_{Z_K}$, for the action of the range of the unit-group map induced by $K\to\mathbb{A}_K$, i.e. of the subgroup of principal ideles $K^\times\subseteq(\mathbb{A}_K)^\times$. Here the idele norm of $x\in(\mathbb{A}_K)^\times$ is the real number obtained from the distributive Haar character $\mathrm{distribHaarChar}(\mathbb{A}_K)(x)\in\mathbb{R}_{\ge0}$ describing how scaling by $x$ distorts Haar measure on $\mathbb{A}_K$, and $\mathrm{centralScalar}$ sends $z$ to the scalar matrix $z\cdot 1$ in $\mathrm{GL}_2(\mathbb{A}_K)$. The conclusion is that the real number obtained from the $\nu_{Z_K}$-measure of the set of $z\in\Omega_K$ whose idele norm of $\det(z\cdot 1)$ lies in the closed interval $[\alpha,\beta]$ is strictly positive; since the real coercion of $\infty$ is $0$, this asserts both positivity and finiteness of that measure.
--
--   This is the positivity (and finiteness) of the band constant attached to a fundamental domain for $K^\times$ acting on the ideles, the band being cut out by the condition that the idele norm of the determinant of the central scalar in $\mathrm{GL}_2(\mathbb{A}_K)$ lie between $\alpha$ and $\beta$. It supplies the nonvanishing normalising factor used in the adelic integral identities for automorphic forms on $\mathrm{GL}_2$ over $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_toReal_measure_inter_ideleNorm_det_centralScalar_mem_Icc_pos_of_isFundamentalDomain.lean

import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open scoped NNReal

theorem NumberField.toReal_measure_inter_ideleNorm_det_centralScalar_mem_Icc_pos_of_isFundamentalDomain
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK) :
    0 < (νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (AutomorphicForm.centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal := by sorry
