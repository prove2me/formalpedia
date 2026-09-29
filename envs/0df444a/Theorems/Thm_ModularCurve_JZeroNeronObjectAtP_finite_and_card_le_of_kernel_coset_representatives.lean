-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives
-- name    : ModularCurve.JZeroNeronObjectAtP.finite_and_card_le_of_kernel_coset_representatives
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/d6c94f91-f11f-5ba5-9ea5-b2be90754305
-- title:
--   Counting A-integral m-torsion in the joint degeneracy kernel
-- statement:
--   Let $N_0$ be a nonzero natural number and $p$ a prime with $p \nmid N_0$, let $A$ be a valuation subring of an algebraic closure of $\mathbf Q$ in which $p$ is a non-unit (`A.LiesOverPrime p`), and write $\kappa$ for the residue field of $A$. Let $\Lambda$ be level data for $(N_0,p,A)$ over `base p`: a morphism $\sigma_A$ with `barPt A ≫ Λ.σA = genPt p`, a scheme $X$ with $f : X \to$ `base p`, a relative group law $\Lambda.L$ on $f$, and bijections $\Lambda.\mathrm{pts}$, $\Lambda.\mathrm{ptsSp}$ of `JZero N₀` and of `JZeroC κ N₀` with the sections of $f$ over `genPt p` and over `resPt A ≫ Λ.σA` respectively; $\Lambda$ is assumed Jacobian, i.e. $f$ carries an abelian-scheme property bundle, $\Lambda.L$ is commutative, $\Lambda.\mathrm{pts}$ and $\Lambda.\mathrm{ptsSp}$ are additive, $\Lambda.\mathrm{pts}$ is Galois-equivariant, reduction of points agrees modulo the maximal ideal when the relevant inputs hold, and every Hecke operator is realised by an endomorphism of $f$ (these conditions are summarised here). Let $O$ be a `JZeroNeronObjectAtP` for these data, with group scheme $O.g : O.G \to$ `base p` carrying a commutative relative group law $O.L$, a bijection $O.\mathrm{pts}$ from `JZero (N₀ * p)` to the sections of $O.g$ over `genPt p`, a toric rank $t = O.\mathrm{toricRank}$, two degeneracy morphisms $O.\mathrm{degeneracyHom}\,i$ from $O.g$ to $\Lambda.f$ ($i \in$ `Fin 2`), and a morphism $O.\mathrm{torusFibre}$ from the split torus of rank $t$ over $\kappa$ into the base change of $O.g$ along `resPt A ≫ Λ.σA`. Let $S$ be a finite set of $\kappa$-points of $O.g$ over `resPt A ≫ Λ.σA` such that (i) composing any $s \in S$ with either degeneracy morphism gives the unit section of $\Lambda.L$ over `resPt A ≫ Λ.σA`, and (ii) every $\kappa$-point $x$ of $O.g$ over `resPt A ≫ Λ.σA` whose composites with both degeneracy morphisms are that unit section becomes, after passage to the fibre over $\kappa$, the $O.L$-product of some $\kappa$-point of the rank-$t$ torus pushed forward by $O.\mathrm{torusFibre}$ with the fibre point of some $s \in S$. Then for every $m > 0$ the set of classes $x$ in `JZero (N₀ * p)` (the degree-zero divisor class group of the level-$N_0p$ modular function field over the algebraic closure of $\mathbf Q$) which lie in the $m$-torsion, whose section $O.\mathrm{pts}\,x$ extends to a section of $O.g$ over $\Lambda.\sigma_A$ in the sense of `ExtendsToPlace`, and which are annihilated by both degeneracy pushforward homomorphisms `degeneracyPushforwardPair N₀ p 0` and `degeneracyPushforwardPair N₀ p 1`, is finite, and its cardinality is at most $|S| \cdot m^{t}$.
--
--   This is the scheme-theoretic counting step underlying the toric-rank estimate: the $A$-integral $m$-torsion classes killed by both degeneracy pushforwards are bounded by the number of torus cosets in the joint kernel of the degeneracy morphisms times $m^{t}$. It is used by [`ModularCurve.JZeroNeronObjectAtP.exists_nsmul_mem_toricPts_of_mem_finPts`](thm.html#ModularCurve.JZeroNeronObjectAtP.exists_nsmul_mem_toricPts_of_mem_finPts).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_ToricDescentData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.finite_and_card_le_of_kernel_coset_representatives
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (S : Finset (SchemeHomOver (resPt A ≫ Λ.σA) O.g))
    (hSK : ∀ s ∈ S, ∀ i, NeronModelInfra.schemeHomOverComp s (O.degeneracyHom i) = Λ.L.one (resPt A ≫ Λ.σA))
    (hS : ∀ x : SchemeHomOver (resPt A ≫ Λ.σA) O.g,
        (∀ i, NeronModelInfra.schemeHomOverComp x (O.degeneracyHom i) = Λ.L.one (resPt A ≫ Λ.σA)) →
        ∃ s ∈ S, ∃ τ : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank),
          toFibrePt x = (O.L.baseChange (resPt A ≫ Λ.σA)).mul (𝟙 _)
            (NeronModelInfra.schemeHomOverComp τ O.torusFibre) (toFibrePt s))
    (m : ℕ) (hm : 0 < m) :
    {x : JZero (N₀ * p) | x ∈ jZeroTorsion (N₀ * p) m ∧ ExtendsToPlace A Λ.σA (O.pts x) ∧
        degeneracyPushforwardPair N₀ p 0 x = 0 ∧ degeneracyPushforwardPair N₀ p 1 x = 0}.Finite ∧
      Nat.card {x : JZero (N₀ * p) | x ∈ jZeroTorsion (N₀ * p) m ∧ ExtendsToPlace A Λ.σA (O.pts x) ∧
        degeneracyPushforwardPair N₀ p 0 x = 0 ∧ degeneracyPushforwardPair N₀ p 1 x = 0} ≤
        S.card * m ^ O.toricRank := by sorry
