-- Prove2me | Theorems.Thm_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC
-- name    : ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/5c5901a4-f792-5831-8754-7e1169231eb4
-- title:
--   Places over j=j₀ as cyclic N-subgroups of E₀
-- statement:
--   Let $K$ be an algebraically closed field, $N \ge 1$ an integer with $N \ne 0$ in $K$, and $j_0 \in K$; let $E_0$ be an elliptic Weierstrass curve over $K$ with $j(E_0) = j_0$. Write $F =$ `modularFunctionFieldFullC K N` for the intermediate field of $K((q))$ generated over $K$ by the series $\mathrm{qExpand}\,K\,d\,(j(q))$ for the nonzero divisors $d \mid N$, where $j(q) = q^{-1}\cdot(E_4^3 \cdot \eta^{-1}\text{-unit})$ is `jqModC K`, and let $j \in F$ denote $j(q)$ itself. A place of $F/K$ is a proper valuation subring of $F$ containing $K$ that is a principal ideal ring, and $\operatorname{ord}_P$ is the associated normalised integer valuation. Let $S$ be a finite set of places of $F/K$ consisting exactly of those $P$ with $\operatorname{ord}_P(j - j_0) > 0$. Then there is a map $f$ from the set $X$ of additive subgroups $H \le E_0(K)$ that are cyclic with $\#H = N$ to places of $F/K$ such that: $f$ takes values in $S$; every member of $S$ is a value of $f$; $f(H) = f(H')$ holds if and only if there is a variable change $\gamma$ over $K$ with $\gamma \cdot E_0 = E_0$ such that every $T \in H$ has $\mathrm{vcInvFun}\,\gamma\,E_0\,T$, i.e. the point $(u^{-2}(x-r),\,u^{-3}(y-t-s(x-r)))$, equal (as a heterogeneous identity of points of $(\gamma\cdot E_0)$ and of $E_0$) to some $T' \in H'$; and for every $H$, $\operatorname{ord}_{f(H)}(j - j_0)$ equals the cardinality of the fibre $\{H' \in X : f(H') = f(H)\}$, viewed as an integer.
--
--   This is the modular interpretation, with ramification indices, of the fibre over $j_0$ of the $j$-map on the $q$-expansion model of $X_0(N)$ over an algebraically closed field in which $N$ is invertible: the places dividing $j - j_0$ correspond to the orbits of the automorphisms of $E_0$ (realised as variable changes fixing $E_0$) on the cyclic subgroups of order $N$ of $E_0(K)$, and the order of vanishing at such a place is the size of the corresponding orbit. It is used downstream to count the places of the level-$N$ modular function field lying over a given $j$-value and to compute orders of vanishing of modular functions at such places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine

theorem ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (j₀ : K) (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hE₀ : E₀.j = j₀)
    (S : Finset (Place K (modularFunctionFieldFullC K N)))
    (hS : ∀ P, P ∈ S ↔
      0 < P.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) -
        algebraMap K (modularFunctionFieldFullC K N) j₀)) :
    ∃ f : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} →
        Place K (modularFunctionFieldFullC K N),
      (∀ H, f H ∈ S) ∧ (∀ P ∈ S, ∃ H, f H = P) ∧
      (∀ H H', f H = f H' ↔ ∃ γ : VariableChange K, γ • E₀ = E₀ ∧
        ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ E₀.toAffine T) T') ∧
      ∀ H, (f H).ord ((⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) -
          algebraMap K (modularFunctionFieldFullC K N) j₀) =
        (Nat.card {H' : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} //
          f H' = f H} : ℤ) := by sorry
