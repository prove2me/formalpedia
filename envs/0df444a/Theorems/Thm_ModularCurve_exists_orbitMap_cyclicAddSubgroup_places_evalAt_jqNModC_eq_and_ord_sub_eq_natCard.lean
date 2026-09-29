-- Prove2me | Theorems.Thm_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard
-- name    : ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/98c58c7b-f6db-5968-a094-0175f3199e58
-- title:
--   Orbit map on X₀(N): j_N-values and dual ramification
-- statement:
--   Let $K$ be an algebraically closed field, let $N\ge 1$ with $N\ne 0$ in $K$, let $j_0\in K$ and let $E_0$ be an elliptic Weierstrass curve over $K$ with $j(E_0)=j_0$. Write $F=$ `modularFunctionFieldFullC K N` for the subfield of $K((q))$ generated over $K$ by the series $\mathrm{qExpand}_d(j(q))$ for the divisors $d\mid N$, where $j(q)=$ `jqModC K` $=q^{-1}E_4^3\eta^{-24}$, and let $j$, $j_N$ denote the elements $\mathrm{qExpand}_1 (j(q))$, $\mathrm{qExpand}_N(j(q))$ of $F$; places of $F/K$ are valuation subrings containing $K$, proper, with principal ideals, and $\mathrm{ord}$ is minus the logarithm of the associated adic valuation. Let $S$ be a finite set of places of $F/K$ whose members are exactly the places $P$ with $\mathrm{ord}_P(j-j_0)>0$. Then there is a map $f$ from the cyclic subgroups $H$ of $E_0(K)$ of order $N$ to places of $F/K$ such that: (1) $f$ takes values in $S$; (2) every place in $S$ is a value of $f$; (3) $f(H)=f(H')$ if and only if there is a variable change $\gamma$ over $K$ with $\gamma\cdot E_0=E_0$ carrying, via `Point.vcInvFun`, each point of $H$ to a point of $H'$; (4) $\mathrm{ord}_{f(H)}(j-j_0)$ equals the number of $H'$ with $f(H')=f(H)$; (5) for each generator $Q$ of $H$ of additive order $N$ whose Vélu full-kernel quotient $E_0/\langle Q\rangle=$ `E₀.fullKernelQuotient Q N` has $\Delta\ne 0$, the value of $f(H)$ at $j_N$ (the residue-field evaluation, defined to be $0$ off the valuation subring) is $j(E_0/\langle Q\rangle)$; and (6) for such $Q$ and any additive homomorphism $\varphi:E_0(K)\to (E_0/\langle Q\rangle)(K)$ with kernel $\langle Q\rangle$ given off $\langle Q\rangle$ by the Vélu translation-sum formula on both coordinates (with $(0,0)$ assigned to the point at infinity), $\mathrm{ord}_{f(H)}\bigl(j_N-j(E_0/\langle Q\rangle)\bigr)$ equals the number of cyclic order-$N$ subgroups $H''$ of $(E_0/\langle Q\rangle)(K)$ for which some variable change $\gamma$ fixing $E_0/\langle Q\rangle$ carries $\varphi(P)$ into $H''$ for every $N$-torsion point $P$ of $E_0(K)$.
--
--   This is the Kronecker–Igusa moduli dictionary for the full level-$N$ modular function field, in the form used to identify the places of $F/K$ above $j=j_0$ with orbits of cyclic $N$-subgroups of $E_0$, together with the transposed data at the second coordinate: the place attached to $(E_0,H)$ has $j_N$-value $j(E_0/H)$ and its ramification over the $j_N$-line is the orbit size of the dual kernel. It feeds the computations of $j_N$-side evaluations and ramification indices used in [`ModularCurve.evalAt_jNGeomGen_eq_zero_of_mem_ssPlaces_of_lt_five`](thm.html#ModularCurve.evalAt_jNGeomGen_eq_zero_of_mem_ssPlaces_of_lt_five) and [`ModularCurve.placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq`](thm.html#ModularCurve.placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine

theorem ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard
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
      (∀ H, (f H).ord ((⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) -
          algebraMap K (modularFunctionFieldFullC K N) j₀) =
        (Nat.card {H' : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} //
          f H' = f H} : ℤ)) ∧

      (∀ (H : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N})
          (Q : E₀.toAffine.Point), H.1 = AddSubgroup.zmultiples Q → addOrderOf Q = N →
          ∀ hΔ : (E₀.fullKernelQuotient Q N).Δ ≠ 0,
          (f H).evalAt (⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ :
              modularFunctionFieldFullC K N)
            = @WeierstrassCurve.j K _ (E₀.fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔ⟩) ∧

      (∀ (H : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N})
          (Q : E₀.toAffine.Point), H.1 = AddSubgroup.zmultiples Q → addOrderOf Q = N →
          ∀ (hΔ : (E₀.fullKernelQuotient Q N).Δ ≠ 0)
            (φ : E₀.toAffine.Point →+ (E₀.fullKernelQuotient Q N).toAffine.Point),
            φ.ker = AddSubgroup.zmultiples Q →
            (∀ P : E₀.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
              (φ P).coordsOrZero =
                (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
                    ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
                 P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
                    ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2))) →
              (f H).ord ((⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ :
                    modularFunctionFieldFullC K N) -
                  algebraMap K (modularFunctionFieldFullC K N)
                    (@WeierstrassCurve.j K _ (E₀.fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔ⟩)) =
                (Nat.card {H'' : {H'' : AddSubgroup (E₀.fullKernelQuotient Q N).toAffine.Point //
                      IsAddCyclic H'' ∧ Nat.card H'' = N} //
                    ∃ γ : VariableChange K, γ • (E₀.fullKernelQuotient Q N) = E₀.fullKernelQuotient Q N ∧
                      ∀ P : E₀.toAffine.Point, N • P = 0 → ∃ T' ∈ H''.1,
                        HEq (Point.vcInvFun γ (E₀.fullKernelQuotient Q N).toAffine (φ P)) T'} : ℤ)) := by sorry
