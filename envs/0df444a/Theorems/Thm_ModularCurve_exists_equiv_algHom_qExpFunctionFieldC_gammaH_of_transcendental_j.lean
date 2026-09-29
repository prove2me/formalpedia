-- Prove2me | Theorems.Thm_ModularCurve_exists_equiv_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j
-- name    : ModularCurve.exists_equiv_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/63b62056-29a3-501e-aff6-7a8977ca913f
-- title:
--   Level-Γ_H(M) structures as K(j)-embeddings of the modular function field
-- statement:
--   Let $K$ be an algebraically closed field, $M\ge 1$ an integer with $M\neq 0$ in $K$, and $H\le(\mathbb Z/M)^\times$ a subgroup; write $\Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb Z)$ consisting of the elements of $\Gamma_0(M)$ whose associated unit $d \bmod M$ lies in $H$. Let $F=$ `qExpFunctionFieldC K (CohCarrier.GammaH M H)` be the subfield of $K((q))$ generated over $K$ by the quotients $\bar p_f/\bar p_g$ of the coefficientwise reductions to $K$ of integral $q$-expansions $p_f,p_g\in\mathbb Z[[q]]$ of modular forms $f,g$ of one and the same weight on $\Gamma_H(M)$, with $\bar p_g\neq0$, and let $x\in F$ be an element whose Laurent series is $q^{-1}\cdot\overline{E_4^3\eta^{-24}}$, the reduction to $K$ of the $q$-expansion of $j$. Let $K\subseteq k\subseteq\Omega$ be a tower of fields, $E$ an elliptic Weierstrass curve over $k$ with $j(E)$ transcendental over $K$, and assume the group of affine points of $E_\Omega$ killed by $M$ has exactly $M^2$ elements. Then there is a bijection $\Phi$ from the set of subsets of $E_\Omega$ of the form $\{\,u\cdot P: u\in H\sqcup\langle-1\rangle\,\}$ (scalars taken as natural-number representatives), $P$ of exact additive order $M$, onto the set of $K$-algebra homomorphisms $\psi\colon F\to\Omega$ with $\psi(x)=j(E)$, such that for every $\sigma\in\mathrm{Aut}_k(\Omega)$ and every pair $s,s'$ of such subsets with $s'$ the image of $s$ under the map on points induced by $\sigma$, one has $\Phi(s')=\sigma\circ\Phi(s)$ as $K$-algebra maps.
--
--   This is the Kroneckerian dictionary at level $\Gamma_H(M)$ in the form due to Igusa and Shimura: the $K(j)$-embeddings into $\Omega$ of the function field of the model of $X_H(M)$ with rational cusp at infinity correspond, Galois-equivariantly, to the $\Gamma_H(M)$-level structures up to sign on an elliptic curve with transcendental $j$-invariant. It is used in the passage from such level structures to places of the modular function field, via [`ModularCurve.exists_orbitMap_torsionOrbit_places_qExpFunctionFieldC_gammaH`](thm.html#ModularCurve.exists_orbitMap_torsionOrbit_places_qExpFunctionFieldC_gammaH).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_equiv_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine
open scoped MatrixGroups

universe u v in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_equiv_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (H : Subgroup (ZMod M)ˣ)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M H)) (hx : (x : LaurentSeries K) = jqModC K)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // M • P = 0} = M ^ 2) :
    ∃ Φ : {s : Set (E.baseChange Ω).toAffine.Point // ∃ P : (E.baseChange Ω).toAffine.Point,
            addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}} ≃
        {ψ : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] Ω // ψ x = algebraMap k Ω E.j},
      ∀ (σ : Ω ≃ₐ[k] Ω)
        (s s' : {s : Set (E.baseChange Ω).toAffine.Point // ∃ P : (E.baseChange Ω).toAffine.Point,
            addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}}),
        s'.1 = (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)) '' s.1 →
          ((Φ s').1 : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] Ω) =
            ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp (Φ s).1 := by sorry
