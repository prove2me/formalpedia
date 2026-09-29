-- Prove2me | Theorems.Thm_ModularCurve_Period_exists_perfectPairing_parabolicHoms_baseChange
-- name    : ModularCurve.Period.exists_perfectPairing_parabolicHoms_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/8e12c5d0-e1e2-5d94-86d6-b5f121996ba1
-- title:
--   Base change of a perfect pairing on integral parabolic homomorphisms
-- statement:
--   Let $\Gamma$ be a subgroup of finite index in $\mathrm{SL}_2(\mathbb{Z})$, and for a commutative ring $R$ write $P(R)$ for the $R$-module [`ModularCurve.Period.parabolicHoms R Γ R`](def/ModularCurve_PeriodMap.html#L62) of additive homomorphisms $\varphi$ from the additive group $\Gamma$ (written additively) to $R$ which satisfy $\varphi(\gamma)=0$ for every $\gamma\in\Gamma$ whose underlying integral matrix has $(\operatorname{tr}\gamma)^2=4$. Let $\mathrm{IP}\colon P(\mathbb{Z})\to_{\mathbb{Z}} P(\mathbb{Z})\to_{\mathbb{Z}}\mathbb{Z}$ be a $\mathbb{Z}$-bilinear form such that both $\mathrm{IP}$ and its flip are bijective as maps $P(\mathbb{Z})\to\operatorname{Hom}_{\mathbb{Z}}(P(\mathbb{Z}),\mathbb{Z})$, and let $R$ be a commutative ring whose additive group is torsion-free. Then there is an $R$-bilinear form $B$ on $P(R)$ such that: both $B$ and its flip are bijective onto $\operatorname{Hom}_R(P(R),R)$; $B(x',y')=\mathrm{IP}(x,y)$ in $R$ whenever $x',y'\in P(R)$ are the images of $x,y\in P(\mathbb{Z})$ under post-composition with the canonical map $\mathbb{Z}\to R$; and, for $T,T'$ endomorphisms of $P(\mathbb{Z})$ adjoint for $\mathrm{IP}$, i.e. $\mathrm{IP}(Tx,y)=\mathrm{IP}(x,T'y)$ for all $x,y$, and $R$-linear endomorphisms $S,S'$ of $P(R)$ such that $Sx'$ is the image of $Tx$ and $S'x'$ the image of $T'x$ whenever $x'$ is the image of $x$, one has $B(Sx',y')=B(x',S'y')$ for all $x',y'\in P(R)$.
--
--   The module $P(R)$ plays the role of the parabolic cohomology $H^1_{\mathrm{par}}(\Gamma,R)$ realised as homomorphisms $\Gamma\to R$ vanishing on elements of trace $\pm 2$, and the statement is the base-change step for a unimodular pairing on it, transporting perfectness and adjoint pairs (Hecke and diamond operators together with their transposes) from $\mathbb{Z}$ to any torsion-free coefficient ring. It is used in the construction of a perfect antisymmetric pairing on the relevant corner submodule of $H^1$ in the non-Eisenstein case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_Period_exists_perfectPairing_parabolicHoms_baseChange.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.Period.exists_perfectPairing_parabolicHoms_baseChange
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (IP : ModularCurve.Period.parabolicHoms ℤ Γ ℤ →ₗ[ℤ] ModularCurve.Period.parabolicHoms ℤ Γ ℤ →ₗ[ℤ] ℤ)
    (hIP : Function.Bijective IP) (hIPf : Function.Bijective IP.flip)
    (R : Type*) [CommRing R] [IsAddTorsionFree R] :
    ∃ B : ModularCurve.Period.parabolicHoms R Γ R →ₗ[R] ModularCurve.Period.parabolicHoms R Γ R →ₗ[R] R,
      Function.Bijective B ∧ Function.Bijective B.flip ∧
      (∀ (x y : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) (x' y' : ModularCurve.Period.parabolicHoms R Γ R),
        ((x' : ModularCurve.Period.parabolicHoms R Γ R) : Additive Γ →+ R) =
          (Int.castAddHom R).comp ((x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ) →
        ((y' : ModularCurve.Period.parabolicHoms R Γ R) : Additive Γ →+ R) =
          (Int.castAddHom R).comp ((y : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ) →
        B x' y' = (IP x y : R)) ∧
      (∀ (T T' : ModularCurve.Period.parabolicHoms ℤ Γ ℤ →ₗ[ℤ] ModularCurve.Period.parabolicHoms ℤ Γ ℤ)
          (S S' : ModularCurve.Period.parabolicHoms R Γ R →ₗ[R] ModularCurve.Period.parabolicHoms R Γ R),
        (∀ x y : ModularCurve.Period.parabolicHoms ℤ Γ ℤ, IP (T x) y = IP x (T' y)) →
        (∀ (x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) (x' : ModularCurve.Period.parabolicHoms R Γ R),
          ((x' : ModularCurve.Period.parabolicHoms R Γ R) : Additive Γ →+ R) =
            (Int.castAddHom R).comp ((x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ) →
          ((S x' : ModularCurve.Period.parabolicHoms R Γ R) : Additive Γ →+ R) =
            (Int.castAddHom R).comp ((T x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ)) →
        (∀ (x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) (x' : ModularCurve.Period.parabolicHoms R Γ R),
          ((x' : ModularCurve.Period.parabolicHoms R Γ R) : Additive Γ →+ R) =
            (Int.castAddHom R).comp ((x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ) →
          ((S' x' : ModularCurve.Period.parabolicHoms R Γ R) : Additive Γ →+ R) =
            (Int.castAddHom R).comp ((T' x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ)) →
        ∀ x' y' : ModularCurve.Period.parabolicHoms R Γ R, B (S x') y' = B x' (S' y')) := by sorry
