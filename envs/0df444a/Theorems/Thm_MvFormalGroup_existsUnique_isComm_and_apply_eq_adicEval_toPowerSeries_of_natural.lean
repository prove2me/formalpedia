-- Prove2me | Theorems.Thm_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural
-- name    : MvFormalGroup.existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/6bdee32e-1ece-5295-8fc5-f8dece2f9f30
-- title:
--   Functorial group law on nilpotents is a unique commutative formal group
-- statement:
--   Let $\mathcal O$ be a commutative ring (in a fixed universe), $p$ a prime such that $(p:\mathcal O)$ is a non-zero-divisor and $\mathcal O$ is adically complete for the ideal $(p)$, and let $d$ be a natural number. Suppose given, for every commutative $\mathcal O$-algebra $g$ in that universe, a binary operation $\mu_g$ on $d$-tuples $\mathrm{Fin}\,d \to g$, subject to the following requirements, all imposed only for those $g$ that are finite and free as $\mathcal O$-modules and only for tuples all of whose entries lie in the radical of the ideal $(p)$ of $g$: $\mu_g$ carries such a pair of tuples to such a tuple; $\mu_g(x,0)=x=\mu_g(0,x)$; $\mu_g$ is associative; $\mu_g$ is commutative; and $\mu$ is natural, in the sense that $\mu_{g'}(\varphi\circ x,\varphi\circ y)=\varphi\circ\mu_g(x,y)$ for every $\mathcal O$-algebra homomorphism $\varphi: g \to g'$ between two such algebras. Then there is exactly one $\Phi : \mathrm{MvFormalGroup}\ d\ \mathcal O$, that is, a $d$-tuple $\Phi_i$ of power series in the variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ over $\mathcal O$ with zero constant term, with the coefficient of each first-copy variable $X_j$ and of each second-copy variable $Y_j$ in $\Phi_i$ equal to $\delta_{ij}$, and satisfying the substitution identity $\Phi(\Phi(X,Y),Z)=\Phi(X,\Phi(Y,Z))$, such that: $\Phi$ is commutative, i.e. interchanging the two copies of the variables fixes each $\Phi_i$; and for every finite free $g$ as above and all tuples $x,y$ with every entry nilpotent, $\mu_g(x,y)_i$ equals [`MvFormalGroup.adicEval`](def/MvFormalGroup_PointsV2.html#L20) of $\Phi_i$ at the combined tuple $(x,y)$, the evaluation of the power series in $g$ along $\mathcal O \to g$ taken with respect to the $(p)$-adic topology on $g$.
--
--   This is the representability (Yoneda) statement for formal group laws: a group law on nilpotent $d$-tuples, functorial in finite free $\mathcal O$-algebras, comes from a unique commutative $d$-dimensional formal group law over $\mathcal O$. It serves as the bridge from functorially defined group laws to formal group laws, and is used by the variant [`MvFormalGroup.existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural_of_mem_radical`](thm.html#MvFormalGroup.existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural_of_mem_radical), in which the identity is asserted on tuples with entries in the radical of $(p)$ rather than only on nilpotent tuples.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.lean

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem MvFormalGroup.existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (d : ℕ)
    (μ : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (Fin d → g) → (Fin d → g) → (Fin d → g))
    (hμ_mem : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
      (x y : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) →
      ∀ j, μ g x y j ∈ (Ideal.span {(p : g)}).radical)
    (hμ_zero : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
      (x : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → μ g x 0 = x ∧ μ g 0 x = x)
    (hμ_assoc : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
      (x y z : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) →
      (∀ j, z j ∈ (Ideal.span {(p : g)}).radical) → μ g (μ g x y) z = μ g x (μ g y z))
    (hμ_comm : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
      (x y : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) → μ g x y = μ g y x)
    (hμ_nat : ∀ (g g' : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
      [CommRing g'] [Algebra 𝓞 g'] [Module.Free 𝓞 g'] [Module.Finite 𝓞 g']
      (φ : g →ₐ[𝓞] g') (x y : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) →
      μ g' (φ ∘ x) (φ ∘ y) = φ ∘ μ g x y) :
    ∃! Φ : MvFormalGroup d 𝓞, Φ.IsComm ∧
      ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
        (x y : Fin d → g), (∀ j, IsNilpotent (x j)) → (∀ j, IsNilpotent (y j)) →
        ∀ i, μ g x y i =
          MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim x y) (Φ.toPowerSeries i) := by sorry
