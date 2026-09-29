-- Prove2me | Theorems.Thm_MvFormalGroup_exists_deformations_dualNumber_span_of_forall_isSymmTwoCocycle
-- name    : MvFormalGroup.exists_deformations_dualNumber_span_of_forall_isSymmTwoCocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/a1ab4689-34e6-55a7-b6bb-15744770f917
-- title:
--   Deformations over dual numbers spanned by nr explicit ones
-- statement:
--   Let $k$ be a commutative ring, $n$ a natural number and $F_0$ an $n$-dimensional formal group law over $k$, i.e. an $n$-tuple of power series in two blocks $X,Y$ of $n$ variables each, with zero constant term, with the linear coefficient of $X_j$ (resp. $Y_j$) in the $i$-th series equal to $\delta_{ij}$, and associative; assume $F_0$ commutative, i.e. interchanging the two blocks fixes each series. Let $r$ be a natural number and $\Gamma_1,\dots,\Gamma_r$ power series in the two blocks which are symmetric normalised $2$-cocycles for $F_0$: zero constant term, invariant under swapping the blocks, and $\Gamma_j(F_0(X,Y),Z)+\Gamma_j(X,Y)=\Gamma_j(X,F_0(Y,Z))+\Gamma_j(Y,Z)$. Assume every symmetric normalised $2$-cocycle $\Gamma'$ for $F_0$ can be written $\Gamma'=\sum_j c_j\Gamma_j+\partial g$ with $c_j\in k$ and $g$ a power series in one block with zero constant term, where $\partial g(X,Y)=g(F_0(X,Y))-g(X)-g(Y)$. Then there are $d\le nr$ formal group laws $D_1,\dots,D_d$ of dimension $n$ over the dual numbers $k[\varepsilon]$, each commutative and each reducing to $F_0$ under the ring map $k[\varepsilon]\to k$ killing $\varepsilon$, such that for every commutative $n$-dimensional formal group law $F$ over $k[\varepsilon]$ reducing to $F_0$ there exist scalars $c_1,\dots,c_d\in k$, a formal group law $G$ of dimension $n$ over $k[\varepsilon]$ and a homomorphism $\theta\colon G\to F$ of formal group laws over $k[\varepsilon]$ (an $n$-tuple of series in one block with zero constant term, compatible with the two group laws) with the $i$-th series of $G$ equal to the image of the $i$-th series of $F_0$ under $k\to k[\varepsilon]$ plus $\sum_j c_j$ times the difference of the $i$-th series of $D_j$ and that image, and with each series of $\theta$ reducing modulo $\varepsilon$ to the variable $X_i$. The conclusion asserts neither that $G$ is commutative nor that $\theta$ is an isomorphism.
--
--   This is the Lubin–Tate dictionary between first-order deformations of a commutative formal group law and symmetric normalised $2$-cocycles, in the form that turns a spanning set of $r$ cocycle classes into at most $nr$ deformations spanning all first-order deformations up to a homomorphism trivial modulo $\varepsilon$. It is applied in [`MvFormalGroup.exists_deformations_dualNumber_span_of_finrank_quotient_span_nthSeries_eq_pow`](thm.html#MvFormalGroup.exists_deformations_dualNumber_span_of_finrank_quotient_span_nthSeries_eq_pow), where the spanning hypothesis is supplied by a dimension count.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_exists_deformations_dualNumber_span_of_forall_isSymmTwoCocycle.lean

import Mathlib
import Definitions.Def_MvFormalGroup_TwoCocycle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open DualNumber in

theorem MvFormalGroup.exists_deformations_dualNumber_span_of_forall_isSymmTwoCocycle
    {k : Type u} [CommRing k] {n : ℕ} (F₀ : MvFormalGroup n k) [F₀.IsComm]
    (r : ℕ) (Γ : Fin r → MvPowerSeries (Fin n ⊕ Fin n) k) (hΓ : ∀ j, F₀.IsSymmTwoCocycle (Γ j))
    (hspan : ∀ Γ' : MvPowerSeries (Fin n ⊕ Fin n) k, F₀.IsSymmTwoCocycle Γ' →
      ∃ (c : Fin r → k) (g : MvPowerSeries (Fin n) k), MvPowerSeries.constantCoeff g = 0 ∧
        Γ' = ∑ j, c j • Γ j + F₀.addCoboundary g) :
    ∃ (d : ℕ) (D : Fin d → MvFormalGroup n (DualNumber k)),
      d ≤ n * r ∧
      (∀ j, (D j).IsComm ∧ (D j).map (TrivSqZeroExt.fstHom k k k).toRingHom = F₀) ∧
      ∀ (F : MvFormalGroup n (DualNumber k)) [F.IsComm],
        F.map (TrivSqZeroExt.fstHom k k k).toRingHom = F₀ →
        ∃ (c : Fin d → k) (G : MvFormalGroup n (DualNumber k)) (θ : G.Hom F),
          (∀ i, G.toPowerSeries i =
            MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries i) +
              ∑ j, c j • ((D j).toPowerSeries i -
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries i))) ∧
          ∀ i, MvPowerSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom (θ.toPowerSeries i) =
            MvPowerSeries.X i := by sorry
