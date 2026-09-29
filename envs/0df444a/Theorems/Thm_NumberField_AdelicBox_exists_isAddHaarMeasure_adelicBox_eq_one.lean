-- Prove2me | Theorems.Thm_NumberField_AdelicBox_exists_isAddHaarMeasure_adelicBox_eq_one
-- name    : NumberField.AdelicBox.exists_isAddHaarMeasure_adelicBox_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/d88a3d5c-bcbb-5d57-a65a-b9377f1a6a55
-- title:
--   Existence of a Haar measure giving the adelic box measure one
-- statement:
--   Let $K$ be a number field, and equip its adele ring $\mathbb{A}_K =$ `AdeleRing (𝓞 K) K` with a measurable space structure which is assumed to be the Borel $\sigma$-algebra of its topology. The assertion is that there exists a measure $\mu_K$ on $\mathbb{A}_K$ which is an additive Haar measure (in Mathlib's sense: a left-invariant, regular measure, positive on nonempty open sets and finite on compact sets) and which satisfies $\mu_K(\mathrm{adelicBox}\,K) = 1$. Here [`NumberField.AdelicBox.adelicBox K`](def/NumberField_AdelicBox.html#L295) is the set of adeles $x = (x_\infty, x_{\mathrm{fin}})$, with $\mathbb{A}_K$ presented as the product of the infinite and finite adele rings, such that: the infinite component $x_\infty$ lies in `infiniteBox K`, the preimage under the ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace K` from the infinite adele ring to the mixed space $\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$ of the $\mathbb{Z}$-span fundamental domain of the lattice basis `mixedEmbedding.latticeBasis K` of the image of $\mathcal{O}_K$; and the finite component $x_{\mathrm{fin}}$ lies in `integralFiniteAdeles (𝓞 K) K`, i.e. $x_{\mathrm{fin}}(v) \in \mathcal{O}_{K_v}$ for every height-one prime $v$ of $\mathcal{O}_K$. No explicit description of $\mu_K$ is given: only its existence is asserted.
--
--   This is the standard normalisation of additive Haar measure on the adeles of a number field, fixed by declaring the product of a fundamental domain for $\mathcal{O}_K$ in the mixed space with the maximal compact subring of the finite adeles to have total mass one. It supplies the normalising hypothesis used by the adelic integration arguments for automorphic forms on $\mathrm{GL}_2$, namely the computations of unipotent-cell integrals against constant terms, the finiteness of a twisted centraliser integral, and the fundamental-domain rate estimate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicBox_exists_isAddHaarMeasure_adelicBox_eq_one.lean

import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem NumberField.AdelicBox.exists_isAddHaarMeasure_adelicBox_eq_one (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)] :
    ∃ μK : Measure (AdeleRing (𝓞 K) K), μK.IsAddHaarMeasure ∧ μK (NumberField.AdelicBox.adelicBox K) = 1 := by sorry
