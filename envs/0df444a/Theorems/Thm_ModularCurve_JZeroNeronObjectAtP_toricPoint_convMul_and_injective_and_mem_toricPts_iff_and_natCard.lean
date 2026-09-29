-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
-- name    : ModularCurve.JZeroNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/7124ea57-a50d-5b23-a573-78f5187f1e10
-- title:
--   Toric points: a character group mapping isomorphically onto T̃[m]
-- statement:
--   Fix natural numbers $N₀$ and $p$ with $N₀,p \neq 0$, $p$ prime and $p \nmid N₀$, a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $p$ in the sense that $p$ is a nonunit of $A$, level data $\Lambda$ for $(N₀,p,A)$ satisfying the predicate `IsJacobian` (the bundled requirements that $\Lambda.f$ is an abelian scheme with commutative relative group law, that the bijections $\Lambda$.`pts` and $\Lambda$.`ptsSp` are additive and Galois-equivariant, that reduction of points agrees modulo $\ell$, and that Hecke operators are realised by endomorphisms over the base), a Néron object $O$ over this data, and an integer $m > 0$. Writing $t = O$.`toricRank` and $\mu\text{-coordinate ring } A[(\mathbb Z/m)^t]$ for the additive monoid algebra `muCoord`, the assertion is fourfold, for the map $\chi \mapsto O$.`toricPoint`$\,m\,hm\,\chi$ from $A$-algebra homomorphisms $A[(\mathbb Z/m)^t] \to \overline{\mathbb Q}$ to the degree-zero divisor class group $J_0(N₀p) =$ `JZero (N₀ * p)`: it is additive for the convolution product on characters carried by `WithConv`; it is injective; a point of `JZero (N₀ * p)` lies in the subgroup $O$.`toricPts`$\,m$ (the closure of the range of the toric point map) exactly when it is in that range; and $O$.`toricPts`$\,m$ has cardinality $m^{t}$.
--
--   This identifies the $m$-torsion of the toric part of the Néron object at $p$ with the character group of $\mu_m^t$ over $\overline{\mathbb Q}$, so that the toric subgroup is an explicit $(\mathbb Z/m)^t$ worth of points of $J_0(N₀p)$. It is used in the analysis of the Galois and Hecke action on these points, in particular by the results computing Frobenius and Hecke operators on elements of `toricPts` and by the extraction of a section and torus point from such an element.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (m : ℕ) (hm : 0 < m) :
    (∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
        O.toricPoint m hm (χ * χ').ofConv = O.toricPoint m hm χ.ofConv + O.toricPoint m hm χ'.ofConv) ∧
    Function.Injective (O.toricPoint m hm) ∧
    (∀ x : JZero (N₀ * p), x ∈ O.toricPts m ↔ ∃ χ, O.toricPoint m hm χ = x) ∧
    Nat.card ↥(O.toricPts m) = m ^ O.toricRank := by sorry
