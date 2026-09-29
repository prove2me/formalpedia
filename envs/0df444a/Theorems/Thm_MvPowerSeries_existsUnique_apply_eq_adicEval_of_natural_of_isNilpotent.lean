-- Prove2me | Theorems.Thm_MvPowerSeries_existsUnique_apply_eq_adicEval_of_natural_of_isNilpotent
-- name    : MvPowerSeries.existsUnique_apply_eq_adicEval_of_natural_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/e6130bd4-4379-5b10-aa61-a784d24c6ec8
-- title:
--   Yoneda lemma for formal affine space on nilpotent ideals
-- statement:
--   Let $R$ be a commutative ring (in a fixed universe $u$) and let $\sigma$ be a finite type of variables. Suppose given a family $t$ assigning to every commutative ring $C$ in the universe $u$ equipped with an $R$-algebra structure, every ideal $J \subseteq C$ and every tuple $x : \sigma \to C$ an element $t_{C,J}(x) \in C$. Assume $t$ is natural on nilpotent thickenings, in the following sense: for all such $R$-algebras $C, C'$, all ideals $J \subseteq C$, $J' \subseteq C'$ with $J$ and $J'$ nilpotent, every $R$-algebra homomorphism $\varphi : C \to C'$ carrying $J$ into $J'$, and every $x : \sigma \to C$ with $x_s \in J$ for all $s$, one has $t_{C',J'}(\varphi \circ x) = \varphi\bigl(t_{C,J}(x)\bigr)$. Then there is exactly one multivariate power series $f \in R[[X_s : s \in \sigma]]$ such that for every $R$-algebra $C$ in the universe $u$, every nilpotent ideal $J \subseteq C$ and every $x : \sigma \to C$ with all $x_s \in J$, the value $t_{C,J}(x)$ equals [`MvFormalGroup.adicEval J x f`](def/MvFormalGroup_PointsV2.html#L20), that is, the evaluation of $f$ at $x$ along $\mathrm{algebraMap}\ R\ C$ computed with the discrete uniformity on $R$ and the $J$-adic topology on $C$. No condition is imposed on the values of $t_{C,J}$ at ideals that are not nilpotent or at tuples with entries outside $J$.
--
--   This is the Yoneda lemma for the formal affine space $\operatorname{Spf} R[[X_s : s \in \sigma]]$, viewed as the functor sending a pair (commutative $R$-algebra $C$, nilpotent ideal $J \subseteq C$) to $J^{\sigma}$: a rule on such pairs that is natural in the pair is given by evaluation of a unique power series. It is the representability input used to pass between functorial data on nilpotent thickenings and power-series identities, and is invoked in the Čerednik–Drinfel'd part of the development, for instance in the treatment of formal $\mathcal{O}_D$-modules and of rigidifications of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_existsUnique_apply_eq_adicEval_of_natural_of_isNilpotent.lean

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvPowerSeries.existsUnique_apply_eq_adicEval_of_natural_of_isNilpotent
    {R : Type u} [CommRing R] {σ : Type} [Finite σ]
    (t : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (σ → C) → C)
    (ht_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C']
      (J : Ideal C) (J' : Ideal C'), IsNilpotent J → IsNilpotent J' →
      ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : σ → C, (∀ s, x s ∈ J) → t C' J' (φ ∘ x) = φ (t C J x)) :
    ∃! f : MvPowerSeries σ R,
      ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
        ∀ x : σ → C, (∀ s, x s ∈ J) → t C J x = MvFormalGroup.adicEval J x f := by sorry
