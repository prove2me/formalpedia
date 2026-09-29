-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_toricLift_of_torusFibre
-- name    : ModularCurve.JHNeronObjectAtP.exists_toricLift_of_torusFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/c7c76b88-193e-5c53-af21-72b319671c55
-- title:
--   Toric lifts μ_m^t → G_A over a place above p
-- statement:
--   Fix a prime $p$, a nonzero modulus $M$ with $p \mid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$. Let $g : G \to \operatorname{Spec}\mathbb{Z}_{(p)}$ (the base being the spectrum of the rationals with denominator coprime to $p$) be smooth, separated and quasi-compact, carrying a commutative relative group law $L$, functorial in sections, such that for every $n > 0$ the multiplication-by-$n$ endomorphism `L.schemeNsmul n` is flat and locally quasi-finite. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ and $\Lambda$ level data for $(p, M, H, A)$, supplying a structure morphism $\sigma_A : \operatorname{Spec} A \to \operatorname{Spec}\mathbb{Z}_{(p)}$ with $\mathrm{barPt}(A) \circ \sigma_A$ the generic point, a scheme $\Lambda.f$ over the base with relative group law $\Lambda.L$, and points dictionaries. Assume a bijection $\mathrm{pts}$ from $J_H(M) = \mathrm{Pic}^0$ of the function field of $X_H$ over $\overline{\mathbb{Q}}$ onto the sections of $g$ over the generic point, additive for $L$ and equivariant for $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ acting on sections by composition with $\operatorname{Spec}(\sigma)$. Assume a toric rank $t$ and a section $\tau$ of the base change of $g$ along $\mathrm{resPt}(A) \circ \sigma_A$ defined on the split torus $\operatorname{Spec} \kappa[\mathbb{Z}^t]$, $\kappa$ the residue field of $A$, which is a closed immersion and is multiplicative on $\kappa$-characters (indexed by `WithConv` of the algebra maps $\kappa[\mathbb{Z}^t] \to \kappa$). Assume finally two coordinates $\mathrm{abq}_0, \mathrm{abq}_1$ from the base change of $g$ to the base change of $\Lambda.f$ over $\kappa$ such that, for every scheme $T$ over $\kappa$, a $T$-point of the base change of $g$ is killed by both coordinates precisely when it factors through $\tau$, and such that each $\mathrm{abq}_i$ commutes with precomposition by twists $\beta$ of the residue point. The conclusion asserts the existence of sections $\iota_m$, for each $m > 0$, of the base change of $g$ along $\sigma_A$ defined on $\operatorname{Spec} A[(\mathbb{Z}/m)^t]$, with six properties: each $\iota_m$ is a closed immersion; each is multiplicative on the $\overline{\mathbb{Q}}$-valued characters $A[(\mathbb{Z}/m)^t] \to \overline{\mathbb{Q}}$ via `muPt`, for the base-changed group law; $\iota_{m'}$ restricts to $\iota_m$ along the inclusion $\mu_m^t \to \mu_{m'}^t$ when $m \mid m'$; reducing modulo the maximal ideal of $A$, the composite of $\iota_m$ with the projection to $G$ agrees with $\mu_m^t \to \mathbb{G}_m^t$ followed by $\tau$ and the projection to $G$; for $\sigma$ in the inertia subgroup at $A$ and $c$ with $\sigma\zeta = \zeta^c$ for all $\zeta$ with $\zeta^m = 1$, the class in $J_H(M)$ attached by $\mathrm{pts}^{-1}$ to $\chi$ composed with $\iota_m$ satisfies $\sigma \cdot x = c \cdot x$; and for $\sigma$ in the decomposition subgroup at $A$ and any $\chi$ there is a character $\chi'$ with $\sigma \cdot x_\chi = x_{\chi'}$.
--
--   This is the construction of the toric part of the Néron object of $J_H(M)$ at a prime $p$ exactly dividing the level: the split torus found in the special fibre at $A$ lifts, over the henselian valuation ring $A$, to closed subgroup schemes $\mu_m^t$ for all $m \ge 1$, compatibly in $m$, with inertia acting on the resulting torsion points through the cyclotomic character and the decomposition group permuting the characters. It feeds the construction of the level data and the relative sub-Picard dictionary for the de Rham model of $X_H$ at $p$, where this toric description of the $\ell$-divisible toric part is what makes the local behaviour at $p$ of the Galois representation accessible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_toricLift_of_torusFibre.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.exists_toricLift_of_torusFibre
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)

    {G : Scheme.{0}} (g : G ⟶ base p) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (L : RelativeGroupLaw (baseRing p) g) (hcomm : L.IsCommutative)

    (nsmul_flat : ∀ n : ℕ, 0 < n → Flat (L.schemeNsmul n))
    (nsmul_locallyQuasiFinite : ∀ n : ℕ, 0 < n → LocallyQuasiFinite (L.schemeNsmul n))

    (A : ValuationSubring (AlgebraicClosure ℚ)) (Λ : JHNeronObjectAtP.LevelData p M H hpM A)

    (pts : JH M H ≃ SchemeHomOver (genPt p) g)
    (hpts_add : ∀ x y : JH M H, pts (x + y) = L.mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M H),
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
