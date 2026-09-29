-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_isFinite_and_locallyOfFinitePresentation_specMap_iota
-- name    : ModularCurve.DRModelPackageLevel.isFinite_and_locallyOfFinitePresentation_specMap_iota
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/8b762888-7971-5e1b-a4e6-ad5fa7444d0d
-- title:
--   Chart inclusions of a Deligne–Rapoport level package are finite
-- statement:
--   Fix a natural number $N_0 \neq 0$ and a prime $q$ with $q \nmid N_0$, and let $\mathfrak P$ be a term of the structure `DRModelPackageLevel N₀ q hqN`, i.e. a bundle of data and properties attached to the Igusa-type scheme $X(N_0,q)$ over $\operatorname{Spec}$ of the ring $R(q)$: properness, flatness, integrality and local finite presentation of the structural morphism to the base, integral closedness of the sections over each affine open, a curve model `Meta` over $\overline{\mathbb Q}$ with function field the base change of the full modular function field of level $N_0 q$ together with an isomorphism onto the corresponding base-changed fibre, compatibility of places with the arithmetic Galois action, a normalisation of $q$-expansions on the finite chart, smoothness of relative dimension $1$ and geometric integrality of the fibre over $\mathbb Q$, sections $\varepsilon_\infty$, $\varepsilon_0$ over the base, and further data including two algebra homomorphisms $\mathfrak P.\mathtt{iota0}$ and $\mathfrak P.\mathtt{iotaInf}$ (the remaining fields are summarised here). The conclusion is the conjunction of two pairs of assertions: the morphism of affine schemes obtained by applying $\operatorname{Spec}$ to the ring homomorphism underlying $\mathfrak P.\mathtt{iota0}$ is finite and locally of finite presentation, and likewise for the ring homomorphism underlying $\mathfrak P.\mathtt{iotaInf}$.
--
--   This records the finiteness and finite presentation of the two chart-level ring inclusions carried by a Deligne–Rapoport level package, the affine shadow of the degeneracy map from level $N_0q$ to level $N_0$ on the finite and the infinite Igusa chart. It is used by [`ModularCurve.DRModelPackageLevel.isFinite_and_locallyOfFinitePresentation_pi`](thm.html#ModularCurve.DRModelPackageLevel.isFinite_and_locallyOfFinitePresentation_pi), which glues the two charts into the corresponding statement for the forgetful morphism $\pi$, and by [`ModularCurve.DRModelPackageLevel.finrank_pi_eq`](thm.html#ModularCurve.DRModelPackageLevel.finrank_pi_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_isFinite_and_locallyOfFinitePresentation_specMap_iota.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
namespace ModularCurve.DRModelPackageLevel

theorem isFinite_and_locallyOfFinitePresentation_specMap_iota (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (𝔓 : DRModelPackageLevel N₀ q hqN) :
    (IsFinite (Spec.map (CommRingCat.ofHom 𝔓.iota0.toRingHom)) ∧
      LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom 𝔓.iota0.toRingHom))) ∧
    (IsFinite (Spec.map (CommRingCat.ofHom 𝔓.iotaInf.toRingHom)) ∧
      LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom 𝔓.iotaInf.toRingHom))) := by sorry
