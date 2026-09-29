-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_isFinite_flat_finrank_pi
-- name    : ModularCurve.DRModelPackageLevel.isFinite_flat_finrank_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/ff84258e-51ec-5cb2-a49f-d6a799d005fe
-- title:
--   Finiteness, flatness and rank q+1 of π
-- statement:
--   Fix a natural number $N_0 \neq 0$ and a prime $q$ with $q \nmid N_0$, and let $\mathfrak{P}$ be a term of the structure `DRModelPackageLevel N₀ q hqN`. That structure bundles, over the Igusa scheme $X(N_0q)$ and its structure morphism `toBase` to $\operatorname{Spec} R(q)$: properness, flatness, local finite presentation of `toBase` and integrality of the source; integral closedness of the sections over every affine open; a curve model `Meta` over $\overline{\mathbb{Q}}$ whose function field is identified with the base change `modularFunctionFieldBar (N₀ * q)` of the modular function field, an isomorphism `eeta` of its underlying scheme with the $\overline{\mathbb{Q}}$-fibre of `toBase` compatible with the structure maps, equivariance of the induced point–place bijection for the arithmetic Galois action, a normalisation of the Igusa chart in terms of Laurent coefficients, smoothness of relative dimension $1$ and geometric integrality of the fibre over $\mathbb{Q}$, sections `εinf`, `εzero` of `toBase`, and further data, among them a morphism $\pi$ over the base whose target is the scheme `DRLevel.X0 N₀ q`. The conclusion asserts that the underlying morphism $\mathfrak{P}.\pi.1$ is finite and locally of finite presentation (the two properties being produced as instances), is flat, and has $\operatorname{finrank}$ equal to $q+1$ at every point $y$ of its target.
--
--   This is the assertion that the forgetful map from the Deligne–Rapoport level model at $N_0q$ to its counterpart at level $N_0$, over $\mathbb{Z}_{(q)}$, is finite locally free of constant rank $q+1 = [\Gamma_0(N_0):\Gamma_0(N_0q)]$. It is packaged in this instance-producing form for use downstream, where the Hecke correspondence at $q$, the associated maps on relative Picard schemes and fibres, and the comparison with Néron models are built from $\pi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_isFinite_flat_finrank_pi.lean

import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
namespace ModularCurve.DRModelPackageLevel

theorem isFinite_flat_finrank_pi (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (𝔓 : DRModelPackageLevel N₀ q hqN) :
    ∃ (_ : IsFinite 𝔓.π.1) (_ : LocallyOfFinitePresentation 𝔓.π.1), Flat 𝔓.π.1 ∧ ∀ y, 𝔓.π.1.finrank y = q + 1 := by sorry
