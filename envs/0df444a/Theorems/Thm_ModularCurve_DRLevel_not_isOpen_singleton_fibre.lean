-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_not_isOpen_singleton_fibre
-- name    : ModularCurve.DRLevel.not_isOpen_singleton_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/0a839fc6-e650-5bea-901e-a87711442f85
-- title:
--   The Igusa fibre has no isolated points
-- statement:
--   Fix natural numbers $N_0$ and $q$ with $N_0$ nonzero and $q$ prime, a field $\kappa$ of characteristic $q$, and a ring homomorphism $\mathrm{to}\kappa \colon$ `DRLevel.R q` $\to \kappa$ from the base ring `DRLevel.R q` of the Igusa model at the prime $q$. Let `DRLevel.fibre toκ` be the scheme-theoretic fibre product, in the category of schemes over $\mathbb{Z}$, of the structure morphism `DRLevel.toBase N₀ q`, which is the Igusa morphism [`ModularCurve.IgusaScheme.igusaTo (N₀ * q) q`](def/ModularCurve_IgusaScheme.html#L277) from [`ModularCurve.DRLevel.X N₀ q`](def/ModularCurve_DRModelPackageLevel.html#L34) to $\operatorname{Spec}$ of `DRLevel.R q`, along $\operatorname{Spec}$ of $\mathrm{to}\kappa$; here the Igusa scheme at level $N$ and prime $\ell$ is the pushout of the two affine morphisms `fFin N ℓ` and `fInf N ℓ` out of `XMid N ℓ`, so it is glued from the spectra of the chart rings `chartAlgFin` and `chartAlgInf`. The assertion is that for every point $w$ of this fibre the singleton $\{w\}$ is not an open subset of the underlying topological space of the fibre; equivalently, the fibre has no isolated point. No hypothesis relating $q$ to $N_0$, in particular no coprimality assumption $q \nmid N_0$, is imposed.
--
--   This is a topological form of the statement that the special fibre of the Igusa model of $X_0(N_0 q)$ at $q$ is everywhere of dimension one, in the spirit of the Deligne–Rapoport and Katz–Mazur descriptions of the reduction of modular curves at a prime dividing the level. It is used in the proof of [`ModularCurve.DRLevel.dense_range_chart_fibre`](thm.html#ModularCurve.DRLevel.dense_range_chart_fibre), and rests on the computation that every localisation of $\kappa \otimes$ `chartAlgFin` or $\kappa \otimes$ `chartAlgInf` at a maximal ideal has Krull dimension one, together with the finite-type property of the two chart algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_not_isOpen_singleton_fibre.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve ModularCurve.DRLevel
open ModularCurve.IgusaScheme

theorem ModularCurve.DRLevel.not_isOpen_singleton_fibre
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
    (κ : Type) [Field κ] [CharP κ q] (toκ : DRLevel.R q →+* κ)
    (w : DRLevel.fibre (N₀ := N₀) toκ) : ¬ IsOpen ({w} : Set (DRLevel.fibre (N₀ := N₀) toκ)) := by sorry
