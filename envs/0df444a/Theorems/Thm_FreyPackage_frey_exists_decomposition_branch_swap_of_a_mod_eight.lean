-- Prove2me | Theorems.Thm_FreyPackage_frey_exists_decomposition_branch_swap_of_a_mod_eight
-- name    : FreyPackage.frey_exists_decomposition_branch_swap_of_a_mod_eight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/696f7461-ef77-517c-9de8-e52ff133dd77
-- title:
--   Frobenius swaps the branches when a ≡ 3 (mod 8)
-- statement:
--   Let $P$ be a Frey package: nonzero integers $a,b,c$, a prime $p \ge 5$ with $a^p + b^p = c^p$, $\gcd(a,b) = 1$, $a \equiv 3 \pmod 4$ and $b \equiv 0 \pmod 2$; assume in addition $a \equiv 3 \pmod 8$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $2$ in the sense that $2$ is a nonunit of $A$. Write $E =$ `P.freyCurveInt` for the integral Weierstrass curve with $a_1 = 1$, $a_2 = (b^p - 1 - a^p)/4$, $a_3 = 0$, $a_4 = -a^p b^p/16$, $a_6 = 0$, and let $E_{\overline{\mathbb{Q}}}$ be its base change along $\mathbb{Z} \to \mathbb{Q} \to \overline{\mathbb{Q}}$. Then there is an element $\sigma$ of the decomposition subgroup of $A$ over $\mathbb{Q}$ (the $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$ preserving $A$) such that for every $p$-torsion point $x \in E_{\overline{\mathbb{Q}}}(\overline{\mathbb{Q}})$, if $x$ does not satisfy `InZeroComponentAt A` then $\sigma \cdot x + x$ does. Here a point satisfies `InZeroComponentAt A` when it is $0$, or is affine, $(x,y)$ with $x \notin A$, or has $x, y \in A$ with residues a nonsingular point of the reduction of $E$ over the residue field of $A$.
--
--   This records the behaviour of the Frey curve at the prime $2$ in the case $a \equiv 3 \pmod 8$, where the reduction is multiplicative but non-split, so that a Frobenius element of the decomposition group interchanges the two branches of the node and hence acts by $-1$ on the quotient of the $p$-torsion by its identity component. It is used by [`FreyPackage.frey_no_cofixed_of_a_mod_eight`](thm.html#FreyPackage.frey_no_cofixed_of_a_mod_eight) to exclude points of $E[p]$ fixed modulo the identity component, a step in the analysis of the local behaviour at $2$ of the mod $p$ representation attached to the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_frey_exists_decomposition_branch_swap_of_a_mod_eight.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem FreyPackage.frey_exists_decomposition_branch_swap_of_a_mod_eight
    (P : FreyPackage) (h8 : (P.a : ZMod 8) = 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 2) :
    ∃ σ ∈ A.decompositionSubgroup ℚ,
      ∀ x : Submodule.torsionBy ℤ
          ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point P.p,
        ¬ P.freyCurveInt.InZeroComponentAt A
            (x : ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) →
          P.freyCurveInt.InZeroComponentAt A
            ((σ • x + x :
              Submodule.torsionBy ℤ
                ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point P.p) :
              ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) := by sorry
