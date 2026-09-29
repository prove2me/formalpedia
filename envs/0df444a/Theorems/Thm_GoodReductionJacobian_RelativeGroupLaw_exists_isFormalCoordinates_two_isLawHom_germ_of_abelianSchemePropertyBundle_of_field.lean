-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isFormalCoordinates_two_isLawHom_germ_of_abelianSchemePropertyBundle_of_field
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isFormalCoordinates_two_isLawHom_germ_of_abelianSchemePropertyBundle_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/6472462b-f380-5d45-963e-f82084e0b7cd
-- title:
--   Formal germ of a homomorphism into a smooth group scheme
-- statement:
--   Let $k$ be a field. Let $f_A : A \to \operatorname{Spec} k$ be a scheme over $k$ equipped with a relative group law $L_A$, i.e. a functorial group structure on the sets of sections $\{\varphi : T \to A \mid \varphi f_A = t\}$ for all $t : T \to \operatorname{Spec} k$, natural in $T$; let $F_A$ be a $2$-dimensional formal group law over $k$ (two power series in $2+2$ variables, with vanishing constant term, identity linear part and associative) and let $\theta_A$ be formal coordinates of dimension $2$ for $f_A$, i.e. an assignment to each $k$-algebra $B'$ and each pair $s \in (B')^2$ of a $B'$-point of $A$, which is assumed to present $L_A$ through $F_A$: compatible with $k$-algebra maps on nilpotent tuples and, for each $B'$ and each ideal $J$ with $J^{n+1}=0$, a bijection from tuples in $J$ onto the points congruent to the identity modulo $J$, carrying the truncated law $F_A$ to $L_A$-multiplication. Let $f' : A' \to \operatorname{Spec} k$ carry a commutative relative group law $L'$, satisfy the project's `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, and admitting some relative group law), and have all fibres of topological Krull dimension $2$. Let $p : A \to A'$ be a morphism over $k$ which is multiplicative for $L_A$ and $L'$ on points over every base. Then there exist a $2$-dimensional formal group law $F'$ over $k$, formal coordinates $\theta''$ of dimension $2$ for $f'$, and a pair $T$ of power series in two variables over $k$ such that $F'$ is commutative, $\theta''$ presents $L'$ through $F'$, $T$ is a homomorphism of laws $F_A \to F'$ (zero constant terms and $T(F_A(x,y)) = F'(T(x),T(y))$), and for every $k$-algebra $B''$, ideal $J$ with $J^{m+1}=0$ and tuple $s$ with entries in $J$, the point $\theta_A(s)$ followed by $p$ equals $\theta''$ evaluated at the truncations $\mathrm{nilEval}\,m\,(T_i)\,s$.
--
--   This is the statement that a homomorphism of relative group laws over a field induces, on infinitesimal neighbourhoods of the identity sections, a homomorphism of the associated formal group laws, with the target's formal group constructed and shown to be $2$-dimensional from smoothness and the fibre dimension. It feeds the construction of formal coordinates on quotients of fake elliptic curves over algebraically closed fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isFormalCoordinates_two_isLawHom_germ_of_abelianSchemePropertyBundle_of_field.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isFormalCoordinates_two_isLawHom_germ_of_abelianSchemePropertyBundle_of_field
    (k : Type) [Field k]

    {A : Scheme.{0}} {fA : A ⟶ Spec (CommRingCat.of k)} (LA : RelativeGroupLaw k fA)
    (FA : MvFormalGroup 2 k) (θA : RelativeGroupLaw.FormalCoordinates fA 2) (hθA : LA.IsFormalCoordinates FA θA)

    {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of k)} (L' : RelativeGroupLaw k f')
    (hL'_comm : L'.IsCommutative) (hA'_bundle : AbelianSchemePropertyBundle k f')
    (hA'_dim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f'.base ⁻¹' {s}) = 2)

    (p : A ⟶ A') (hp : p ≫ f' = fA)
    (hp_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t fA),
      mapPt p hp (LA.mul t P Q) = L'.mul t (mapPt p hp P) (mapPt p hp Q)) :
    ∃ (F' : MvFormalGroup 2 k) (θ'' : RelativeGroupLaw.FormalCoordinates f' 2) (T : Series k),
      F'.IsComm ∧ L'.IsFormalCoordinates F' θ'' ∧ IsLawHom FA F' T ∧
      (∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θA B'' s).1 ≫ p = (θ'' B'' (fun i => MvFormalGroup.nilEval m (T i) s)).1) := by sorry
