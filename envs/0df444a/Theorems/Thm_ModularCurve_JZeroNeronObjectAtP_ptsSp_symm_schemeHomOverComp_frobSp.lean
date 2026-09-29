-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_ptsSp_symm_schemeHomOverComp_frobSp
-- name    : ModularCurve.JZeroNeronObjectAtP.ptsSp_symm_schemeHomOverComp_frobSp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/d2629f37-074c-55ad-9417-a833ba7a2805
-- title:
--   Frobenius commutes with the transported Hecke operator on the reduction
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0\neq 0$ and $p$ prime, and assume $p\nmid N_0$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$ in the sense that $p$ belongs to the nonunits of $A$, and write $\kappa=\mathrm{ResidueField}\,A$. Let $\Lambda$ be a `LevelData` for $(N_0,p,A)$, that is: a morphism $\sigma_A\colon \operatorname{Spec} A\to \mathrm{base}\,p$ with $\mathrm{barPt}\,A$ followed by $\sigma_A$ equal to $\mathrm{genPt}\,p$, a scheme $X$ with a structure morphism $f\colon X\to\mathrm{base}\,p$ carrying a relative group law, a bijection $\Lambda.\mathrm{pts}$ from $\mathrm{JZero}\,N_0=\mathrm{Pic}^0$ of the level-$N_0$ modular function field over $\overline{\mathbb Q}$ onto the sections of $f$ over $\mathrm{genPt}\,p$, and a bijection $\Lambda.\mathrm{ptsSp}$ from $\mathrm{JZeroC}\,\kappa\,N_0=\mathrm{Pic}^0$ of the level-$N_0$ modular function field over $\kappa$ onto the sections of $f$ over $\mathrm{resPt}\,A$ followed by $\sigma_A$; assume $\Lambda.\mathrm{IsJacobian}$ (the abelian-scheme property bundle for $f$, commutativity of the group law, additivity and Galois equivariance of $\Lambda.\mathrm{pts}$, additivity of $\Lambda.\mathrm{ptsSp}$, compatibility of reduction of points mod $\ell$, and realisability of every Hecke element by an endomorphism of $X$ over $\mathrm{base}\,p$). Let $O$ be a `JZeroNeronObjectAtP` for these data, with its operator $O.\mathrm{frobSp}$ on $\mathrm{JZeroC}\,\kappa\,N_0$. Let $t\in\mathrm{HeckeAlg}=\mathbb Z[x_\ell:\ell\text{ prime}]$ and let $\varphi'$ be an endomorphism of $X$ over $\mathrm{base}\,p$ (so $\varphi'$ followed by $f$ is $f$) which realises $t$ on the generic points, i.e. $(\Lambda.\mathrm{pts}(t\cdot x))_1=(\Lambda.\mathrm{pts}\,x)_1$ followed by $\varphi'$ for all $x\in \mathrm{JZero}\,N_0$, for the Hecke module structure `heckeModuleBar`. Then for every $u\in\mathrm{JZeroC}\,\kappa\,N_0$ the transported operator $\bar T_t(u):=\Lambda.\mathrm{ptsSp}^{-1}\bigl(\Lambda.\mathrm{ptsSp}(u)\ \text{followed by}\ \varphi'\bigr)$ satisfies $\bar T_t(O.\mathrm{frobSp}\,u)=O.\mathrm{frobSp}(\bar T_t(u))$.
--
--   This is the commutation of Frobenius with the Hecke correspondences on the reduction of $J_0(N_0)$ at a prime $p\nmid N_0$, in the form needed for the Néron-model bookkeeping at level $N_0p$. It is used in the transport of Hecke support through the abelian quotient, namely in the two statements deducing lower-level torsion, respectively nonvanishing of Hecke torsion, from nonvanishing of `ptsSp.symm` of the fibre map on the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_ptsSp_symm_schemeHomOverComp_frobSp.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP
open ModularCurve

theorem ModularCurve.JZeroNeronObjectAtP.ptsSp_symm_schemeHomOverComp_frobSp
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (t : HeckeAlg) (φ' : SchemeHomOver Λ.f Λ.f)
    (hφ't : letI := heckeModuleBar N₀; ∀ x : JZero N₀, (Λ.pts (t • x)).1 = (Λ.pts x).1 ≫ φ'.1)
    (u : JZeroC (ResidueField ↥A) N₀) :
    Λ.ptsSp.symm (NeronModelInfra.schemeHomOverComp (Λ.ptsSp (O.frobSp u)) φ') =
      O.frobSp (Λ.ptsSp.symm (NeronModelInfra.schemeHomOverComp (Λ.ptsSp u) φ')) := by sorry
