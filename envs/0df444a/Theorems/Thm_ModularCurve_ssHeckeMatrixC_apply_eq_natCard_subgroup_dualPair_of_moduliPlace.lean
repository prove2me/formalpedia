-- Prove2me | Theorems.Thm_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_moduliPlace
-- name    : ModularCurve.ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_moduliPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/54f5118d-bc0b-5acf-9d5a-7f2302b56e12
-- title:
--   Supersingular Hecke matrix entries count ℓ-isogenies preserving Γ₀(N)-structure
-- statement:
--   Let $\kappa$ be an algebraically closed field of prime characteristic $q'$, let $N\ge 1$ with $q'\nmid N$, and let $\ell$ be a prime with $\ell\neq q'$ and $\ell\nmid N$. Write $F_N=$ `modularFunctionFieldC κ N`, the subfield of $\kappa((q))$ generated over $\kappa$ by the two series `jqModC` and `jqNModC … N`, and let the roof `charLDegeneracyRoof κ N ℓ` be generated over $\kappa$ by the series indexed by $1,N,\ell,N\ell$; assume that both legs, the inclusion `heckeAlphaC` and the substitution `heckeBetaC` given by $q\mapsto q^{\ell}$, are integral ring maps ($h\alpha$, $h\beta$). Let $x,y$ be places of $F_N$ lying in `ssPlaces q' N κ`, i.e. satisfying the predicate `IsSupersingularPlace q' N κ`. Let $E_x,E_y$ be elliptic Weierstrass curves over $\kappa$ and $C_x\le E_x(\kappa)$, $C_y\le E_y(\kappa)$ subgroups of the affine point groups which are cyclic of cardinality $N$, and assume that the valuation subring of $x$ (respectively $y$) is the preimage, under the inclusion of $F_N$ into the full modular function field, of the valuation subring of `moduliPlace κ N E_x C_x` (respectively of $(E_y,C_y)$). Then the $(y,x)$ entry of `ssHeckeMatrixC q' κ N ℓ hα hβ`, namely the finite sum over places $W$ of the roof, of the ramification index of $W$ along $\beta$ times the inertia degree of $W$ along $\alpha$, taken over those $W$ whose restrictions along $\beta$ and $\alpha$ are $x$ and $y$, equals the cardinality, as an integer, of the set of subgroups $D$ of the points of $E_x$ base-changed to $\kappa$ with $\#D=\ell$ for which there exist $\psi\in$ [`WeierstrassCurve.rationalHomSet κ E_x E_y`](def/WeierstrassCurve_RationalEnd.html#L28) and $\psi'\in$ [`WeierstrassCurve.rationalHomSet κ E_y E_x`](def/WeierstrassCurve_RationalEnd.html#L28) (each either zero or rationally represented) with $\ker\psi=D$, $\psi'\circ\psi=\ell\cdot\mathrm{id}$, $\psi\circ\psi'=\ell\cdot\mathrm{id}$, and $\psi(T)\in C_y$ for every $T\in C_x$.
--
--   This is the curve side of the Hecke square at level $N$ in characteristic $q'$: it identifies the correspondence-theoretic entry of the supersingular Hecke matrix at $\ell$ with the moduli-theoretic count of $\ell$-isogenies $E_x\to E_y$, equipped with a dual isogeny, that carry the $\Gamma_0(N)$-structure $C_x$ into $C_y$. It is used to match `ssHeckeMatrixC` with a Brandt-type matrix on a quaternionic class set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_moduliPlace.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve AlgebraicCurve

theorem ModularCurve.ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_moduliPlace
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (N : ℕ) [NeZero N] (hq'N : ¬ q' ∣ N)
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q') (hℓN : ¬ ℓ ∣ N)
    (hα : (heckeAlphaC κ N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC κ N ℓ).toRingHom.IsIntegral)
    (x y : ↥(ssPlaces q' N κ))
    (E_x E_y : WeierstrassCurve κ) [E_x.IsElliptic] [E_y.IsElliptic]
    (C_x : AddSubgroup E_x.toAffine.Point) (C_y : AddSubgroup E_y.toAffine.Point)
    (hCx : IsAddCyclic C_x ∧ Nat.card C_x = N) (hCy : IsAddCyclic C_y ∧ Nat.card C_y = N)
    (hx : (x.1).toValuationSubring = (moduliPlace κ N E_x C_x).toValuationSubring.comap
      (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom)
    (hy : (y.1).toValuationSubring = (moduliPlace κ N E_y C_y).toValuationSubring.comap
      (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom) :
    ssHeckeMatrixC q' κ N ℓ hα hβ y x =
      (Nat.card {D : AddSubgroup (E_x.baseChange κ).toAffine.Point //
        Nat.card D = ℓ ∧ ∃ ψ ∈ WeierstrassCurve.rationalHomSet κ E_x E_y, ∃ ψ' ∈ WeierstrassCurve.rationalHomSet κ E_y E_x,
          ψ.ker = D ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧
          ∀ T ∈ C_x, ψ T ∈ C_y} : ℤ) := by sorry
