-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_toricLift_of_torusFibre
-- name    : ModularCurve.JZeroNeronObjectAtP.exists_toricLift_of_torusFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/3a336572-ae2c-5fac-b0c2-9faac6e3e301
-- title:
--   Toric lifts μ_m^t of the special-fibre torus over a place
-- statement:
--   Fix $N_0\ge 1$ and a prime $p$, and let $\mathrm{base}\,p=\operatorname{Spec} R$ with $R\subset\mathbf{Q}$ the subring of rationals whose denominator is coprime to $p$. Let $g\colon G\to\operatorname{Spec} R$ be smooth, separated and quasi-compact, equipped with a commutative relative group law $L$ (functorial multiplication, unit, inverse and naturality on $T$-points) such that for every $n>0$ the morphism `L.schemeNsmul n` $\colon G\to G$ is flat and locally quasi-finite. Let $A$ be a valuation subring of $\overline{\mathbf{Q}}$ with residue field $\kappa$, and $\Lambda$ a `LevelData` $N_0$, $p$, $A$: a structure map $\sigma_A\colon\operatorname{Spec} A\to\operatorname{Spec} R$ with $\operatorname{Spec}\overline{\mathbf{Q}}\to\operatorname{Spec} A\to \operatorname{Spec} R$ the generic point, a scheme $\Lambda.X\to\operatorname{Spec} R$ with relative group law $\Lambda.L$, and dictionaries for $J_0(N_0)$ generically and over $\kappa$. Assume a bijection $\mathrm{pts}\colon J_0(N_0p)=\mathrm{Pic}^0$ of the level-$N_0p$ function field over $\overline{\mathbf{Q}}\;\simeq\;G(\overline{\mathbf{Q}})$ which is additive and Galois-equivariant (with $\sigma$ acting by precomposition with $\operatorname{Spec}\sigma$). Assume further an integer $t$ and a point $\tau$ of the special fibre $G\times_R\kappa$ defined on the split torus $\operatorname{Spec}\kappa[\mathbf{Z}^t]$ over $\kappa$, whose underlying morphism is a closed immersion and which is multiplicative on the characters $\chi$ (composition with the point of $\chi\chi'$ equals the product of the compositions); and two morphisms $\mathrm{abq}_0,\mathrm{abq}_1$ from $G\times_R\kappa$ to $\Lambda.X\times_R\kappa$ over $\kappa$ such that, for every $T\to\operatorname{Spec}\kappa$, a $T$-point $x$ of $G\times_R\kappa$ is annihilated by both $\mathrm{abq}_i$ (compositions equal the unit of the base-changed $\Lambda.L$) if and only if $x$ factors through $\tau$, and such that each $\mathrm{abq}_i$, read as a map on points, commutes with precomposition by any self-map $\beta$ of $\operatorname{Spec}\kappa$ over $\operatorname{Spec} R$. The conclusion asserts the existence, for each $m>0$, of a point $\mathrm{toricLift}\,m$ of $G\times_R A$ defined on $\operatorname{Spec} A[(\mathbf{Z}/m)^t]$ over $A$, such that: its underlying morphism is a closed immersion; it is multiplicative on the $A$-algebra characters $\chi\colon A[(\mathbf{Z}/m)^t]\to\overline{\mathbf{Q}}$; the lifts are compatible with the inclusions $\mu_m^t\hookrightarrow\mu_{m'}^t$ for $m\mid m'$; reduction along $A\to\kappa$ of $\mathrm{toricLift}\,m$ agrees, as a morphism to $G$, with $\mu_m^t\to\mathbf{G}_m^t$ followed by $\tau$; for $\sigma$ in the inertia subgroup of $A$ over $\mathbf{Q}$ and $c\in\mathbf{N}$ with $\sigma\zeta=\zeta^c$ on $m$-th roots of unity, $\sigma$ sends the element of $J_0(N_0p)$ corresponding to the point of $\chi$ to $c$ times it; and for $\sigma$ in the decomposition subgroup, $\sigma$ sends that element to the one attached to some other character $\chi'$.
--
--   This is the construction of Grothendieck's toric part of the special fibre, lifted over a place $A$ of $\overline{\mathbf{Q}}$ to the full system of multiplicative-type subgroups $\mu_m^t$ for all $m>0$ (including powers of $p$), together with the action of inertia (by the cyclotomic character exponent) and of the decomposition group (permuting characters) on the resulting points of $J_0(N_0p)$. It supplies the toric-lift data of the Néron object at $p$ attached to level $N_0p$, and is used in assembling that object from a level model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_exists_toricLift_of_torusFibre.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_toricLift_of_torusFibre
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime]

    {G : Scheme.{0}} (g : G ⟶ base p) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (L : RelativeGroupLaw (baseRing p) g) (hcomm : L.IsCommutative)

    (nsmul_flat : ∀ n : ℕ, 0 < n → Flat (L.schemeNsmul n))
    (nsmul_locallyQuasiFinite : ∀ n : ℕ, 0 < n → LocallyQuasiFinite (L.schemeNsmul n))

    (A : ValuationSubring (AlgebraicClosure ℚ)) (Λ : JZeroNeronObjectAtP.LevelData N₀ p A)

    (pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) g)
    (hpts_add : ∀ x y : JZero (N₀ * p), pts (x + y) = L.mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (N₀ * p)),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)

    (toricRank : ℕ)
    (torusFibre : SchemeHomOver (torusStr (ResidueField ↥A) toricRank)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g))
    (torusFibre_isClosedImmersion : IsClosedImmersion torusFibre.1)
    (torusFibre_mul : ∀ χ χ' : WithConv (torusCoord (ResidueField ↥A) toricRank →ₐ[ResidueField ↥A] ResidueField ↥A),
      NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) torusFibre =
        (L.baseChange (resPt A ≫ Λ.σA)).mul _
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) torusFibre)
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) torusFibre))

    (abqFibre : Fin 2 → SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f))
    (abqFibre_eq_one_iff : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
      (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g)),
      (∀ i, NeronModelInfra.schemeHomOverComp x (abqFibre i) =
          (Λ.L.baseChange (resPt A ≫ Λ.σA)).one s) ↔
        ∃ y : SchemeHomOver s (torusStr (ResidueField ↥A) toricRank),
          NeronModelInfra.schemeHomOverComp y torusFibre = x)
    (abqFibre_twist : ∀ (β : SchemeHomOver (resPt A ≫ Λ.σA) (resPt A ≫ Λ.σA)) (i : Fin 2)
      (x : SchemeHomOver (resPt A ≫ Λ.σA) g),
      fibreMap (abqFibre i) (GoodReductionJacobian.schemeHomOverComp β.1 β.2 x) =
        GoodReductionJacobian.schemeHomOverComp β.1 β.2 (fibreMap (abqFibre i) x)) :
    ∃ toricLift : ∀ m : ℕ, 0 < m →
        SchemeHomOver (muStr ↥A toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA g),

      (∀ (m : ℕ) (hm : 0 < m), IsClosedImmersion (toricLift m hm).1) ∧

      (∀ (m : ℕ) (hm : 0 < m) (χ χ' : WithConv (muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ)),
        NeronModelInfra.schemeHomOverComp (muPt A toricRank m (χ * χ').ofConv) (toricLift m hm) =
          (L.baseChange Λ.σA).mul _
            (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ.ofConv) (toricLift m hm))
            (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ'.ofConv) (toricLift m hm))) ∧

      (∀ (m m' : ℕ) (hm : 0 < m) (hm' : 0 < m') (h : m ∣ m'),
        muIncl ↥A toricRank h ≫ (toricLift m' hm').1 = (toricLift m hm).1) ∧

      (∀ (m : ℕ) (hm : 0 < m),
        muBaseChange (residue ↥A) toricRank m ≫ (toricLift m hm).1 ≫ pullback.fst g Λ.σA =
          muToTorus (ResidueField ↥A) toricRank m ≫ torusFibre.1 ≫ pullback.fst g (resPt A ≫ Λ.σA)) ∧

      (∀ (m : ℕ) (hm : 0 < m), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ m = 1 → σ ζ = ζ ^ c) →
        ∀ χ : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
          σ • pts.symm (genOfBaseChangePt Λ.hσA
              (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ) (toricLift m hm))) =
            c • pts.symm (genOfBaseChangePt Λ.hσA
              (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ) (toricLift m hm)))) ∧

      (∀ (m : ℕ) (hm : 0 < m), ∀ σ ∈ A.decompositionSubgroup ℚ,
        ∀ χ : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
          ∃ χ' : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
            σ • pts.symm (genOfBaseChangePt Λ.hσA
                (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ) (toricLift m hm))) =
              pts.symm (genOfBaseChangePt Λ.hσA
                (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ') (toricLift m hm)))) := by sorry
