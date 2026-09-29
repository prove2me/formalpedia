-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_map_eq_one_or_eq_neg_one_of_isLevelAutAt_one_of_exists_ringHom
-- name    : ModularCurve.FullLevel.AuxLevel.map_eq_one_or_eq_neg_one_of_isLevelAutAt_one_of_exists_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/89326613-4513-5fca-ae75-fed602c46d60
-- title:
--   Faithfulness of the attached level automorphisms mod qℓ
-- statement:
--   Let $q\ge 5$ and $\ell\ge 3$ be distinct primes and $M'$ a nonzero natural number with $q\nmid M'$ and $\ell\nmid M'$. Let $L$ be a field of characteristic $0$, $\xi\in L$ a primitive $(q\ell)$-th root of unity admitting a ring homomorphism $\iota_0:L\to\mathbb{C}$ with $\iota_0(\xi)=\exp(2\pi i/(q\ell))$, and let $K$ be the intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the image, under coefficientwise extension $\mathbb{Q}\to L$, of the $q$-expansion function field [`ModularCurve.xHFunctionField`](def/ModularCurve_XH.html#L79) of level $\Gamma_H$ with $N_0=(q\ell)^2M'$ and $H=\mathrm{levelH}$ the kernel of $(\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$. Let $A$ be a discrete valuation domain with an $L$-algebra structure making $L$ its fraction field, with $q$ in the maximal ideal of $A$, with $\ell$ and $M'$ units in $A$, and acting on $K$ compatibly with $L$; let $j\in K$ have Laurent series the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the $j$-invariant, and assume $j\neq 0$. Let $\gamma\in\mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M')$ and assume `IsLevelAutAt` holds for $\gamma^{-1}$ with the automorphism $\tau=1$ of $K$: for every weight $k$, every pair of modular forms $f,g$ of level $\Gamma_H(N_0,H)$ with integral $q$-expansions $p_f,p_g$, $p_g$ giving a nonzero series, every $x\in K$ whose Laurent series is the image of $p_f/p_g$, and every $\iota:L\to\mathbb{C}$ with $\iota(\xi)=\exp(2\pi i/(q\ell))$, one has $\iota_*(x)\cdot q\text{-exp}(g\mid_k \mathrm{conjElemN}(q\ell,\gamma^{-1}))=q\text{-exp}(f\mid_k \mathrm{conjElemN}(q\ell,\gamma^{-1}))$, where $\mathrm{conjElemN}(m,\delta)=\begin{pmatrix}\delta_{00}&\delta_{01}/m\\ m\delta_{10}&\delta_{11}\end{pmatrix}$. Then the reduction of $\gamma$ in $\mathrm{SL}_2(\mathbb{Z}/q\ell)$ is $1$ or $-1$.
--
--   This is the faithfulness half of the identification of the automorphisms of the rigid level-$q\ell$ function field attached to elements of $\Gamma_0(M')$: if the automorphism attached to $\gamma^{-1}$ is the identity, then $\gamma\equiv\pm 1 \pmod{q\ell}$. Together with the converse it pins down the kernel of the attachment map, and it is used in the count [`ModularCurve.FullLevel.natCard_levelAut_attached_eq_natCard_specialLinearGroup_zmod`](thm.html#ModularCurve.FullLevel.natCard_levelAut_attached_eq_natCard_specialLinearGroup_zmod) of the group of attached automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_map_eq_one_or_eq_neg_one_of_isLevelAutAt_one_of_exists_ringHom.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevel.map_eq_one_or_eq_neg_one_of_isLevelAutAt_one_of_exists_ringHom
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))

    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (h1 : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K 1) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (q * ℓ))) γ = 1 ∨
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (q * ℓ))) γ = -1 := by sorry
