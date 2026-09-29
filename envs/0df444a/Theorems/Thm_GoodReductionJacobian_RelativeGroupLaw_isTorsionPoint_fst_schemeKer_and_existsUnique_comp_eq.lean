-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isTorsionPoint_fst_schemeKer_and_existsUnique_comp_eq
-- name    : GoodReductionJacobian.RelativeGroupLaw.isTorsionPoint_fst_schemeKer_and_existsUnique_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/773986bc-063f-53ec-843d-da0d538f0ce8
-- title:
--   The n-torsion kernel scheme represents n-torsion points
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme, $f \colon A \to \operatorname{Spec} R$ a morphism, $L$ a `RelativeGroupLaw R f` — that is, a choice, for every scheme $T$ and every $t \colon T \to \operatorname{Spec} R$, of a multiplication, a unit and an inversion on the set $\{\varphi \colon T \to A \mid \varphi \circ f = t\}$ of points of $A$ over $t$, satisfying associativity, the two unit laws, left inverse cancellation, and compatibility with precomposition by morphisms $\psi \colon T' \to T$ over $\operatorname{Spec} R$ — and let $n$ be a natural number. Write $[n]$ for `L.schemeNsmul n`, the underlying morphism $A \to A$ of the $n$-th iterate (defined by $0 \mapsto$ unit, $k+1 \mapsto$ product of the $k$-th iterate with the point) of the tautological point $\mathrm{id}_A$ over $f$, write $e$ for `(L.one (𝟙 (Spec (CommRingCat.of R)))).1`, the underlying morphism $\operatorname{Spec} R \to A$ of the unit point over the identity, let `L.schemeKer n` be the fibre product of $[n]$ and $e$, and let `L.schemeKerStr n` be its second projection to $\operatorname{Spec} R$. The assertion is: the first projection $u$ from `L.schemeKer n` to $A$ satisfies $u$ followed by $f$ equals `L.schemeKerStr n`, so that $u$ is a point of $A$ over `L.schemeKerStr n`; moreover (i) this point is $n$-torsion, i.e. its $n$-th iterate under the group law equals the unit point over `L.schemeKerStr n`; and (ii) for every scheme $T$, every $t \colon T \to \operatorname{Spec} R$ and every point $z$ of $A$ over $t$ whose $n$-th iterate is the unit point over $t$, there is a unique morphism $g$ from $T$ to `L.schemeKer n` with $g$ followed by $u$ equal to the underlying morphism of $z$.
--
--   This is the representability of the $n$-torsion subfunctor of a scheme with a relative group law over $\operatorname{Spec} R$: the kernel scheme $A[n]$, formed as the fibre product of multiplication by $n$ and the unit section, together with its tautological point, is a universal $n$-torsion point. It is used in the construction of polarisations on Jacobians with good reduction, where the $2$-torsion kernel scheme is analysed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isTorsionPoint_fst_schemeKer_and_existsUnique_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isTorsionPoint_fst_schemeKer_and_existsUnique_comp_eq
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (n : ℕ) :
    ∃ hu : pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f = L.schemeKerStr n,
      L.IsTorsionPoint (L.schemeKerStr n) n ⟨pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1, hu⟩ ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (z : SchemeHomOver t f), L.IsTorsionPoint t n z →
        ∃! g : T ⟶ L.schemeKer n, g ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 = z.1 := by sorry
