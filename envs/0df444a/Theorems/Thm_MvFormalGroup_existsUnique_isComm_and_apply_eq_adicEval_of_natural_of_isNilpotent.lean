-- Prove2me | Theorems.Thm_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent
-- name    : MvFormalGroup.existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/b7477916-ee9c-549b-807e-2c711e964640
-- title:
--   Yoneda: natural group laws on nilpotent ideals are formal group laws
-- statement:
--   Let $R$ be a commutative ring in a universe $u$ and $d$ a natural number. Suppose given, for every commutative ring $C$ in universe $u$ equipped with an $R$-algebra structure, every ideal $J \subseteq C$ and all $x, y : \mathrm{Fin}\,d \to C$, a tuple $\mu_{C,J}(x,y) : \mathrm{Fin}\,d \to C$, subject to the following hypotheses, each imposed only when $J$ is a nilpotent ideal and only for tuples all of whose entries lie in $J$: all entries of $\mu_{C,J}(x,y)$ again lie in $J$; $\mu_{C,J}(x,0) = x$ and $\mu_{C,J}(0,x) = x$; $\mu_{C,J}(\mu_{C,J}(x,y),z) = \mu_{C,J}(x,\mu_{C,J}(y,z))$; $\mu_{C,J}(x,y) = \mu_{C,J}(y,x)$; and naturality, namely for nilpotent ideals $J \subseteq C$, $J' \subseteq C'$ and an $R$-algebra homomorphism $\varphi : C \to C'$ with $\varphi(J) \subseteq J'$, $\mu_{C',J'}(\varphi \circ x, \varphi \circ y) = \varphi \circ \mu_{C,J}(x,y)$. The conclusion is that there is exactly one $\Phi :$ [`MvFormalGroup d R`](def/MvFormalGroup_BasicV2.html#L15), that is a family $\Phi_i$ ($i \in \mathrm{Fin}\,d$) of multivariate power series over $R$ in the variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ with zero constant term, with the coefficient of $X_{\mathrm{inl}\,j}$ and of $X_{\mathrm{inr}\,j}$ in $\Phi_i$ equal to $1$ if $i = j$ and $0$ otherwise, and satisfying the associativity identity $\Phi(\Phi(X,Y),Z) = \Phi(X,\Phi(Y,Z))$ of substitutions of power series in three groups of $d$ variables, such that in addition $\Phi$ satisfies `IsComm`, i.e. interchanging the two groups of variables fixes each $\Phi_i$, and such that for every nilpotent ideal $J$ in a commutative $R$-algebra $C$ as above, all $x, y$ with entries in $J$ and every $i$, one has $\mu_{C,J}(x,y)_i =$ `adicEval` $J\,(\mathrm{Sum.elim}\,x\,y)\,\Phi_i$, the evaluation of $\Phi_i$ at the point $(x,y)$ via $\mathrm{Sum.elim}$ using the structure map $R \to C$ and the $J$-adic topology on $C$.
--
--   This is the Yoneda-style recognition statement for formal group laws in the form needed over an arbitrary base: a functorial commutative group law on tuples from nilpotent ideals of $R$-algebras is represented by a unique commutative $d$-dimensional formal group law over $R$. It is applied to produce the formal group of the kernel of reduction of a smooth group scheme along a nilpotent ideal, in [`GoodReductionJacobian.RelativeGroupLaw.exists_mvFormalGroup_kernelOfReduction_of_smooth`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_mvFormalGroup_kernelOfReduction_of_smooth); note that no hypothesis of the existence of inverses is imposed, inverses being automatic for formal group laws.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent.lean

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent
    {R : Type u} [CommRing R] (d : ℕ)
    (μ : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (Fin d → C) → (Fin d → C) → (Fin d → C))
    (hμ_mem : ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
      ∀ x y : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) → ∀ j, μ C J x y j ∈ J)
    (hμ_zero : ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin d → C, (∀ j, x j ∈ J) → μ C J x 0 = x ∧ μ C J 0 x = x)
    (hμ_assoc : ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
      ∀ x y z : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) → (∀ j, z j ∈ J) →
        μ C J (μ C J x y) z = μ C J x (μ C J y z))
    (hμ_comm : ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
      ∀ x y : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) → μ C J x y = μ C J y x)
    (hμ_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C']
      (J : Ideal C) (J' : Ideal C'), IsNilpotent J → IsNilpotent J' →
      ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x y : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) →
          μ C' J' (φ ∘ x) (φ ∘ y) = φ ∘ μ C J x y) :
    ∃! Φ : MvFormalGroup d R, Φ.IsComm ∧
      ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
        ∀ x y : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) →
          ∀ i, μ C J x y i = MvFormalGroup.adicEval J (Sum.elim x y) (Φ.toPowerSeries i) := by sorry
