-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_galoisTower_of_continuous_surjective
-- name    : LanglandsTunnell.exists_galoisTower_of_continuous_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/ee17ee9e-6a8a-586b-97d8-c55616b3cdfb
-- title:
--   Continuous surjective mod-3 representations come from finite Galois towers
-- statement:
--   Let $\rho$ be a group homomorphism from the absolute Galois group $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the algebra automorphisms of `AlgebraicClosure ℚ` over $\mathbb{Q}$ with its Krull topology, to the general linear group $\mathrm{GL}_2(\mathbb{Z}/3)$, and suppose $\rho$ is continuous (the finite target carrying the discrete topology) and surjective. The assertion is that there exist an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, a `NumberField` structure on $L$ and a proof that $L$ is Galois over $\mathbb{Q}$, together with a multiplicative isomorphism $e \colon (L \simeq_{\mathbb{Q}} L) \to \mathrm{GL}_2(\mathbb{Z}/3)$ of the Galois group of $L/\mathbb{Q}$ with $\mathrm{GL}_2(\mathbb{Z}/3)$, such that [`LanglandsTunnell.galRep e`](def/LanglandsTunnell_GalRep.html#L17) equals $\rho$; by definition `galRep e` is the restriction homomorphism $\mathrm{AlgEquiv.restrictNormalHom}$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\mathrm{Gal}(L/\mathbb{Q})$ followed by $e$. Thus $\rho$ factors as restriction to a finite Galois extension $L/\mathbb{Q}$ with Galois group identified with $\mathrm{GL}_2(\mathbb{Z}/3)$ via $e$.
--
--   This is the standard statement that a continuous representation of the absolute Galois group of $\mathbb{Q}$ with finite discrete target is cut out by a finite Galois extension, here in the surjective mod-$3$, rank-two case, packaged so that the representation is literally of the form `galRep e`. It feeds the Langlands–Tunnell input of the argument, being used in the construction of the weight-one object whose traces reproduce $\rho$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_GalRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem LanglandsTunnell.exists_galoisTower_of_continuous_surjective
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) (ZMod 3))
    (hcont : Continuous ρ) (hsurj : Function.Surjective ρ) :
    ∃ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField ↥L) (_ : IsGalois ℚ ↥L)
      (e : (↥L ≃ₐ[ℚ] ↥L) ≃* GL (Fin 2) (ZMod 3)), LanglandsTunnell.galRep e = ρ := by sorry
