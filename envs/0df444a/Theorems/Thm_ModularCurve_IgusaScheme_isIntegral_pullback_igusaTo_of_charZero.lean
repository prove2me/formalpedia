-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_isIntegral_pullback_igusaTo_of_charZero
-- name    : ModularCurve.IgusaScheme.isIntegral_pullback_igusaTo_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/76221fa0-b083-5e25-9909-7e1a4901711d
-- title:
--   Characteristic-zero fibres of the Igusa scheme are integral
-- statement:
--   Let $N$ be a natural number with $N \neq 0$, let $\ell$ be a prime with $\ell \nmid N$, and write $\mathbb{Z}_{(\ell)}$ for the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator (in lowest terms) is coprime to $\ell$. Let $K$ be a field of characteristic zero equipped with a $\mathbb{Z}_{(\ell)}$-algebra structure. Recall that [`ModularCurve.IgusaScheme N ℓ`](def/ModularCurve_IgusaScheme.html#L255) is the scheme obtained as the pushout of the two morphisms $\operatorname{Spec}$ of the inclusions of the chart algebras `chartAlgFin N ℓ` and `chartAlgInf N ℓ` (the $\mathbb{Z}_{(\ell)}$-subalgebras of the full modular function field of level $N$ generated relative to $j$ and to $j^{-1}$ respectively) into the common "middle" ring, and that `igusaTo N ℓ` is the structure morphism to $\operatorname{Spec}\mathbb{Z}_{(\ell)}$ obtained by descending the two structure morphisms $\operatorname{Spec}$ of $\mathbb{Z}_{(\ell)} \to$ `chartAlgFin N ℓ` and $\mathbb{Z}_{(\ell)} \to$ `chartAlgInf N ℓ` across the pushout. The assertion is that the scheme underlying the fibre product of `igusaTo N ℓ` with $\operatorname{Spec}$ of the structure map $\mathbb{Z}_{(\ell)} \to K$ is integral, i.e. its underlying space is irreducible and its structure sheaf has no nilpotents.
--
--   This is the characteristic-zero half of the geometric integrality of the Igusa scheme over $\operatorname{Spec}\mathbb{Z}_{(\ell)}$: every fibre over a field of characteristic zero receiving $\mathbb{Z}_{(\ell)}$ is integral. It is used in the proof of [`ModularCurve.IgusaScheme.geometricallyIntegral_igusaTo`](thm.html#ModularCurve.IgusaScheme.geometricallyIntegral_igusaTo) and, through it, in the geometric integrality of the base changes of the two-chart integral model of the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_isIntegral_pullback_igusaTo_of_charZero.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_X0ModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ModularCurve ModularCurve.IgusaScheme

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.IgusaScheme.isIntegral_pullback_igusaTo_of_charZero
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (K : Type) [Field K] [CharZero K] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) K] :
    IsIntegral ↑(pullback (igusaTo N ℓ)
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) K)))) := by sorry
