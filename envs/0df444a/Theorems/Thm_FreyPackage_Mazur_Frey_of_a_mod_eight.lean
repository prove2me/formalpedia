-- Prove2me | Theorems.Thm_FreyPackage_Mazur_Frey_of_a_mod_eight
-- name    : FreyPackage.Mazur_Frey_of_a_mod_eight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/09f0c9d8-93bc-542b-a4de-ea151f356880
-- title:
--   Irreducibility of E_P[p] when a ≡ 3 (mod 8)
-- statement:
--   Let $P$ be a Frey package, i.e. the project's structure [`FreyPackage`](def/FLTPrelim_FreyPackage.html#L17) packaging nonzero integers $a,b,c$, a prime $p$ with $p \ge 5$, a solution $a^p+b^p=c^p$, the coprimality $\gcd(a,b)=1$, and the normalisations $a \equiv 3 \pmod 4$ and $b \equiv 0 \pmod 2$. Assume in addition that the image of $a$ in $\mathbb{Z}/8$ is $3$. The conclusion is `GaloisRepIsIrreducible` for the associated Frey curve over $\mathbb{Q}$, with base field $K =$ `AlgebraicClosure ℚ`, coefficient field $\mathbb{Q}$ and level $n = p$. Here `P.freyCurve` is the Weierstrass curve over $\mathbb{Q}$ with $a_1 = 1$, $a_2 = (b^p - 1 - a^p)/4$, $a_3 = 0$, $a_4 = -a^p b^p/16$, $a_6 = 0$, and the project's predicate `GaloisRepIsIrreducible` unfolds to the conjunction of two assertions about $M :=$ `Submodule.torsionBy ℤ` applied to the group of affine points of the base change of `P.freyCurve` to $\overline{\mathbb{Q}}$ and to $p$, regarded as a module over $\mathbb{Z}/p$: first, $M$ is nontrivial; second, every $\mathbb{Z}/p$-submodule $N \subseteq M$ which is `IsGaloisStable` over $\mathbb{Q}$ — that is, $\sigma \cdot x \in N$ for all $\mathbb{Q}$-algebra automorphisms $\sigma$ of $\overline{\mathbb{Q}}$ and all $x \in N$, the action being induced by `Point.map` on points — equals $\bot$ or $\top$. No continuity condition and no two-dimensionality of $M$ are asserted or assumed; the Galois group is the bare automorphism group $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ as an abstract group.
--
--   This is the $a \equiv 3 \pmod 8$ case of the irreducibility of the mod-$p$ representation attached to the Frey curve, in the form used in the Frey–Serre–Ribet route; in this case the curve has non-split multiplicative reduction at $2$ and a local argument at $2$ suffices, so no appeal to Mazur's theorem on rational isogenies of prime degree is made. Compared with the textbook statement, the formal conclusion is the basis-free assertion that the $p$-torsion of $E_P(\overline{\mathbb{Q}})$ is nontrivial and has no Galois-stable $\mathbb{Z}/p$-submodule other than $0$ and the whole module. It is used as one half of the case split in [`FreyPackage.Mazur_Frey`](thm.html#FreyPackage.Mazur_Frey), which establishes the same irreducibility for an arbitrary Frey package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_Mazur_Frey_of_a_mod_eight.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem FreyPackage.Mazur_Frey_of_a_mod_eight (P : FreyPackage)
    (h8 : (P.a : ZMod 8) = 3) :
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p := by sorry
