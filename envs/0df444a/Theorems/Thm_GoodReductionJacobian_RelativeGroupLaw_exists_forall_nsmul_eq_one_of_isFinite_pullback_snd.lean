-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_forall_nsmul_eq_one_of_isFinite_pullback_snd
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_forall_nsmul_eq_one_of_isFinite_pullback_snd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/88a83c82-62b6-5308-aa1f-4a87c650b430
-- title:
--   Uniform exponent for points killed by a finite-kernel homomorphism
-- statement:
--   Let $K$ be a field, let $fX : X \to \operatorname{Spec} K$ be a scheme over $K$ and let $LX$ be a relative group law on $fX$: a group structure, functorial in the base, on each set of $T$-points $\{\varphi : T \to X \mid \varphi \circ fX = t\}$ for $t : T \to \operatorname{Spec} K$, given by operations `mul`, `one`, `inv` satisfying associativity, the two unit laws and left inverses, and compatible with base change along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Assume $LX$ is commutative, i.e. its multiplication on $T$-points is commutative for every $t$. Let $LY$ be a relative group law on a second $K$-scheme $fY : Y \to \operatorname{Spec} K$, not assumed commutative, and let $u : X \to Y$ satisfy $u$ followed by $fY$ equal to $fX$. Assume $u$ is a homomorphism on points: for all $t : T \to \operatorname{Spec} K$ and all $T$-points $x, y$ of $X$, the composite of $LX.\mathrm{mul}\,t\,x\,y$ with $u$ is $LY.\mathrm{mul}\,t$ applied to the composites of $x$ and of $y$ with $u$. Assume further that the second projection $X \times_{u,Y,e} \operatorname{Spec} K \to \operatorname{Spec} K$ is a finite morphism, where $e$ is the unit $K$-point $LY.\mathrm{one}(\mathrm{id}_{\operatorname{Spec} K})$. Then there is an $N > 0$ such that for every $t : T \to \operatorname{Spec} K$ and every $T$-point $x$ of $X$ whose composite with $u$ is $LY.\mathrm{one}\,t$, the $N$-fold iterate $LX.\mathrm{nsmul}\,t\,N\,x$ (defined by $0 \mapsto LX.\mathrm{one}\,t$ and $n+1 \mapsto LX.\mathrm{mul}\,t$ of the $n$-th iterate with $x$) equals $LX.\mathrm{one}\,t$.
--
--   This is the functor-of-points form of the statement that a finite commutative group scheme over a field has finite exponent (Deligne's theorem gives the order itself as an exponent), applied to the kernel of a homomorphism with finite kernel scheme. It serves to produce quasi-inverses of isogenies, and is used in the study of the fake elliptic curves occurring in the Čerednik–Drinfel'd uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_forall_nsmul_eq_one_of_isFinite_pullback_snd.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_forall_nsmul_eq_one_of_isFinite_pullback_snd
    {K : Type u} [Field K]
    {X : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of K)} (LX : RelativeGroupLaw K fX)
    (hcX : LX.IsCommutative)
    {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of K)} (LY : RelativeGroupLaw K fY)
    (u : SchemeHomOver fX fY)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t fX),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) u =
        LY.mul t (NeronModelInfra.schemeHomOverComp x u) (NeronModelInfra.schemeHomOverComp y u))
    (hker : IsFinite (pullback.snd u.1 (LY.one (𝟙 (Spec (CommRingCat.of K)))).1)) :
    ∃ N : ℕ, 0 < N ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t fX),
        NeronModelInfra.schemeHomOverComp x u = LY.one t → LX.nsmul t N x = LX.one t := by sorry
