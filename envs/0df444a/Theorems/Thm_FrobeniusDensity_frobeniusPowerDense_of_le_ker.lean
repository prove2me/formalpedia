-- Prove2me | Theorems.Thm_FrobeniusDensity_frobeniusPowerDense_of_le_ker
-- name    : FrobeniusDensity.frobeniusPowerDense_of_le_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/88b3b9ff-b59e-5806-89c0-2d47bacc7c1e
-- title:
--   Frobenius-power density for subgroups containing Gal(ℚ̄/F)
-- statement:
--   Let $F$ be a number field which is Galois over $\mathbb Q$, equipped with an embedding into $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` compatible with the $\mathbb Q$-structures, and write $G_{\mathbb Q}$ for the group of $\mathbb Q$-algebra automorphisms of $\overline{\mathbb Q}$. Let $H \le G_{\mathbb Q}$ be a subgroup containing the kernel of the restriction homomorphism `AlgEquiv.restrictNormalHom F` from $G_{\mathbb Q}$ to the automorphisms of $F$, and let $S$ be a finite set of natural numbers. The conclusion is the predicate [`FrobeniusPowerDense S H`](def/GaloisRep_FrobeniusPowerDense.html#L7): for every $\sigma \in G_{\mathbb Q}$ there exist a natural number $\ell$, a valuation subring $A$ of $\overline{\mathbb Q}$, elements $\tau, g \in G_{\mathbb Q}$ and an exponent $n \in \mathbb N$ such that $\ell$ is prime, $\ell \notin S$, $A$ lies over $\ell$ in the sense that the image of $\ell$ in $\overline{\mathbb Q}$ is a non-unit of $A$, $\tau$ is a Frobenius at $A$ for $\ell$, i.e. $\tau$ belongs to the decomposition subgroup of $A$ over $\mathbb Q$ and the induced action of $\tau$ on the residue field of $A$ is $x \mapsto x^{\ell}$, and finally $g\,\tau^{n}\,g^{-1}\,\sigma^{-1} \in H$.
--
--   This is the form of Frobenius's density theorem used as an input elsewhere in the development: modulo the subgroup $H$, every element of $G_{\mathbb Q}$ is matched by a conjugate of a power of a Frobenius element at some prime outside a prescribed finite set. It discharges the hypothesis [`FrobeniusPowerDense`](def/GaloisRep_FrobeniusPowerDense.html#L7) in the identification of traces and determinants of Galois representations agreeing at Frobenius elements, and in the level- and torsion-datum arguments that rest on that identification.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusDensity_frobeniusPowerDense_of_le_ker.lean

import Mathlib
import Definitions.Def_GaloisRep_FrobeniusPowerDense

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FrobeniusDensity.frobeniusPowerDense_of_le_ker (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    [Algebra F (AlgebraicClosure ℚ)] [IsScalarTower ℚ F (AlgebraicClosure ℚ)]
    {H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H)
    (S : Finset ℕ) : FrobeniusPowerDense S H := by sorry
