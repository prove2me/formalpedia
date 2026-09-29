-- Prove2me | Theorems.Thm_ModularCurve_finsum_ramificationIndexAlong_heckeAlphaC_eq_natCard_overgroup_dualPair_of_moduliPlace
-- name    : ModularCurve.finsum_ramificationIndexAlong_heckeAlphaC_eq_natCard_overgroup_dualPair_of_moduliPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/42761467-4b9e-5ab3-b758-a1b0f690ef1d
-- title:
--   Ramification-weighted Hecke fibres count cyclic ℓ-overgroups with dual pairs
-- statement:
--   Let $\kappa$ be an algebraically closed field, $N\ge 1$ an integer, $\ell$ a prime, and assume $N\ell$ is invertible in $\kappa$ (i.e. $(N\ell)\cdot 1_\kappa\neq 0$). Write $F_N=\kappa\bigl(j(q),j(q^N)\bigr)\subseteq \kappa((q))$ for `modularFunctionFieldC` and $R=\kappa\bigl(j(q),j(q^N),j(q^\ell),j(q^{N\ell})\bigr)$ for `charLDegeneracyRoof`, and let $\alpha=$`heckeAlphaC` be the inclusion $F_N\hookrightarrow R$ and $\beta=$`heckeBetaC` the $\kappa$-algebra map induced by the substitution $q\mapsto q^{\ell}$ on Laurent series; both are assumed integral, so that places of $R$ (valuation subrings, proper, containing $\kappa$, with principal ideals) restrict along them by taking preimages of valuation subrings. Let $x,y$ be places of $F_N$ over $\kappa$, let $E_x,E_y$ be elliptic Weierstrass curves over $\kappa$ with $C_x\le E_x(\kappa)$, $C_y\le E_y(\kappa)$ cyclic of order $N$, and assume the valuation subring of $x$ (resp. $y$) is the preimage under the inclusion $F_N\subseteq \kappa(j(q^d):d\mid N)$ of that of `moduliPlace` of the pair $(E_x,C_x)$ (resp. $(E_y,C_y)$). Then the finite sum, over the places $W$ of $R$ with $W|_\beta=x$ and $W|_\alpha=y$, of the ramification index of $W$ along $\alpha$ — the least $n>0$ of the form $\operatorname{ord}_W(\alpha f)$ with $0\neq f\in F_N$ — equals the number of subgroups $C^+\le E_y(\kappa)$ that are cyclic of order $N\ell$, satisfy $\ell C^+=C_y$, and for which there exist homomorphisms $\psi'$ in [`WeierstrassCurve.rationalHomSet`](def/WeierstrassCurve_RationalEnd.html#L28) $\kappa\,E_y\,E_x$ and $\psi$ in [`WeierstrassCurve.rationalHomSet`](def/WeierstrassCurve_RationalEnd.html#L28) $\kappa\,E_x\,E_y$ (each either zero or rationally represented over $\kappa$) with $\ker\psi'=N C^+$, $\psi\circ\psi'=\ell$, $\psi'\circ\psi=\ell$ and $\psi'(C^+)\subseteq C_x$.
--
--   This is the moduli-theoretic evaluation of the transposed Hecke correspondence at level $N$ on the degeneracy roof: the coefficient of $x$ in $\beta_*\alpha^*(y)$, weighted by ramification along the inclusion leg, is computed as a count of cyclic order-$N\ell$ overgroups of the level structure equipped with a dual pair of $\ell$-isogenies. It is the curve-side input to [`ModularCurve.ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_dvd_of_five_le_of_moduliPlace`](thm.html#ModularCurve.ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_dvd_of_five_le_of_moduliPlace), which evaluates the supersingular Hecke matrix at a prime dividing the level, the case in which the two legs of the roof are no longer interchanged by an automorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finsum_ramificationIndexAlong_heckeAlphaC_eq_natCard_overgroup_dualPair_of_moduliPlace.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve AlgebraicCurve
open Classical in

theorem ModularCurve.finsum_ramificationIndexAlong_heckeAlphaC_eq_natCard_overgroup_dualPair_of_moduliPlace
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (N : ℕ) [NeZero N] (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hNℓ : ((N * ℓ : ℕ) : κ) ≠ 0)
    (hα : (heckeAlphaC κ N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC κ N ℓ).toRingHom.IsIntegral)
    (x y : Place κ ↥(modularFunctionFieldC κ N))
    (E_x E_y : WeierstrassCurve κ) [E_x.IsElliptic] [E_y.IsElliptic]
    (C_x : AddSubgroup E_x.toAffine.Point) (C_y : AddSubgroup E_y.toAffine.Point)
    (hCx : IsAddCyclic C_x ∧ Nat.card C_x = N) (hCy : IsAddCyclic C_y ∧ Nat.card C_y = N)
    (hx : x.toValuationSubring = (moduliPlace κ N E_x C_x).toValuationSubring.comap
      (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom)
    (hy : y.toValuationSubring = (moduliPlace κ N E_y C_y).toValuationSubring.comap
      (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom) :
    (∑ᶠ W : Place κ ↥(charLDegeneracyRoof κ N ℓ),
        if W.restrictAlong (heckeBetaC κ N ℓ) hβ = x ∧ W.restrictAlong (heckeAlphaC κ N ℓ) hα = y then
          (W.ramificationIndexAlong (heckeAlphaC κ N ℓ) : ℤ) else 0) =
      (Nat.card {Cp : AddSubgroup E_y.toAffine.Point //
        (IsAddCyclic Cp ∧ Nat.card Cp = N * ℓ) ∧ Cp.map (ℓ • AddMonoidHom.id _) = C_y ∧
        ∃ ψ' ∈ WeierstrassCurve.rationalHomSet κ E_y E_x, ∃ ψ ∈ WeierstrassCurve.rationalHomSet κ E_x E_y,
          ψ'.ker = Cp.map (N • AddMonoidHom.id _) ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧
          ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ∀ T ∈ Cp, ψ' T ∈ C_x} : ℤ) := by sorry
