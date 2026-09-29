-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_isIntegral_pullback_igusaTo_of_charP
-- name    : ModularCurve.IgusaScheme.isIntegral_pullback_igusaTo_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/056ec0bb-bc2b-533f-aa8e-3548ab025392
-- title:
--   Integrality of the characteristic-ℓ fibres of the Igusa scheme
-- statement:
--   Fix a natural number $N \neq 0$ and a prime $\ell$ with $\ell \nmid N$, and write $\mathbb{Z}_{(\ell)}$ for the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $\ell$. Let $K$ be a field of characteristic $\ell$ equipped with a $\mathbb{Z}_{(\ell)}$-algebra structure. Consider the structure morphism `igusaTo N ℓ` from [`ModularCurve.IgusaScheme N ℓ`](def/ModularCurve_IgusaScheme.html#L255) to $\operatorname{Spec} \mathbb{Z}_{(\ell)}$: here [`ModularCurve.IgusaScheme N ℓ`](def/ModularCurve_IgusaScheme.html#L255) is the pushout, in schemes, of the two morphisms `fFin N ℓ` and `fInf N ℓ` from the spectrum of the middle ring to the spectra of the two chart algebras `chartAlgFin N ℓ` and `chartAlgInf N ℓ` — the $\mathbb{Z}_{(\ell)}$-subalgebras `chartAlg` of the full modular function field of level $N$ attached to $j$ and to $j^{-1}$ respectively — and `igusaTo N ℓ` is the morphism obtained from the two structure maps of $\mathbb{Z}_{(\ell)}$ into these chart algebras, which agree on the middle ring. The assertion is that the fibre product of this morphism with $\operatorname{Spec}$ of the structure homomorphism $\mathbb{Z}_{(\ell)} \to K$ is, as a scheme, integral, i.e. irreducible and reduced.
--
--   This is the statement that the special fibre at $\ell$ of the Igusa (integral model) scheme of level $N$, base changed to an arbitrary field of characteristic $\ell$ with $\ell \nmid N$, is an integral scheme; it is the characteristic-$\ell$ half of the geometric integrality of the Igusa scheme over $\mathbb{Z}_{(\ell)}$. It is used in the study of the Deligne–Rapoport model and of sections and closed immersions into the fibres, and thereby in the good-reduction analysis of the Jacobian at primes not dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_isIntegral_pullback_igusaTo_of_charP.lean

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

theorem ModularCurve.IgusaScheme.isIntegral_pullback_igusaTo_of_charP
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (K : Type) [Field K] [CharP K ℓ] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) K] :
    IsIntegral ↑(pullback (igusaTo N ℓ)
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) K)))) := by sorry
