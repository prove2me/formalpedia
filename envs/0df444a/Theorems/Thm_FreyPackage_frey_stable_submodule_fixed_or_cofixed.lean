-- Prove2me | Theorems.Thm_FreyPackage_frey_stable_submodule_fixed_or_cofixed
-- name    : FreyPackage.frey_stable_submodule_fixed_or_cofixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/0d15255a-bf0d-573b-a00d-743b349a6611
-- title:
--   Fixed-or-cofixed dichotomy for stable submodules of Frey p-torsion
-- statement:
--   Let $P$ be a [`FreyPackage`](def/FLTPrelim_FreyPackage.html#L17): integers $a,b,c$, all nonzero, a prime $p \ge 5$, with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a \equiv 3 \pmod 4$ and $b \equiv 0 \pmod 2$; write $E =$ `P.freyCurve` for the associated Weierstrass curve over $\mathbb{Q}$ with $a_1 = 1$, $a_2 = (b^p-1-a^p)/4$, $a_3 = 0$, $a_4 = -a^pb^p/16$, $a_6 = 0$. The module of $p$-torsion is taken to be `Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p`, the subgroup of points of the affine curve over a fixed algebraic closure of $\mathbb{Q}$ killed by $p$, equipped with the project's $\mathbb{Z}/p$-module structure and with the action of the group $(\overline{\mathbb{Q}}) \simeq_{\text{alg}[\mathbb{Q}]} (\overline{\mathbb{Q}})$ of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$ by application of the automorphism to the coordinates. Let $N$ be a $\mathbb{Z}/p$-submodule of this $p$-torsion which is `IsGaloisStable` over $\mathbb{Q}$ — that is, $\sigma \bullet x \in N$ for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ and every $x \in N$ — and suppose $N \neq \bot$ and $N \neq \top$. The conclusion is a disjunction: either every $\sigma$ fixes every element of $N$ pointwise, $\sigma \bullet x = x$ for all $x \in N$; or every $\sigma$ acts trivially modulo $N$, i.e. $\sigma \bullet x - x \in N$ for every element $x$ of the whole $p$-torsion. Note that no one-dimensionality of $N$ is assumed (only that it is a proper nonzero submodule), and the Galois group appears purely as an abstract automorphism group, with no continuity hypothesis.
--
--   Classically this is the step, in Serre's analysis of reducible mod $p$ representations of semistable elliptic curves and in its use by Darmon, Diamond and Taylor, that a Galois-stable line in $E[p]$ for the Frey curve gives diagonal characters one of which is trivial: $N$ consists of rational points or $E[p]/N$ is fixed. The formal statement is shaped as a dichotomy about a proper nonzero $\mathbb{Z}/p$-submodule $N$ rather than about characters, and the second alternative is expressed by the condition $\sigma \bullet x - x \in N$ on all of $E[p]$ instead of by triviality of the quotient character. It is used to produce a Galois-stable cofixed line when the mod $p$ representation of the Frey curve is not irreducible, in [`FreyPackage.frey_reducible_hasCofixedLine`](thm.html#FreyPackage.frey_reducible_hasCofixedLine).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem FreyPackage.frey_stable_submodule_fixed_or_cofixed (P : FreyPackage) (N : Submodule (ZMod P.p) (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p)) (hN : IsGaloisStable (K := AlgebraicClosure ℚ) ℚ N) (hbot : N ≠ ⊥) (htop : N ≠ ⊤) : (∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), ∀ x ∈ N, σ • x = x) ∨ (∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), ∀ x : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p, σ • x - x ∈ N) := by sorry
