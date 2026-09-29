-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_inertia_smul_eq_and_exists_decomposition_smul_eq_of_muLift
-- name    : ModularCurve.JZeroNeronObjectAtP.inertia_smul_eq_and_exists_decomposition_smul_eq_of_muLift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/5f9f8932-d158-507d-9a27-e54184bf1009
-- title:
--   Galois action on toric μ_m-points: inertia and decomposition
-- statement:
--   Fix a natural number $N_0 \neq 0$ and a prime $p$, and write $\mathrm{base}\,p = \operatorname{Spec} \mathbb{Z}_{(p)}$, where $\mathbb{Z}_{(p)}$ is the subring of $\mathbb{Q}$ of fractions whose denominator is coprime to $p$. Let $g : G \to \mathrm{base}\,p$ be smooth, separated and quasi-compact, and let $L$ be a commutative relative group law on $g$ over $\mathbb{Z}_{(p)}$ (functorial multiplication, unit, inverse on $T$-points, natural in $T$) such that each multiplication morphism `L.schemeNsmul n`, $n > 0$, is flat and locally quasi-finite. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, with residue field $\kappa$, and let $\Lambda$ be a `LevelData N₀ p A`, supplying in particular a structure morphism $\sigma_A : \operatorname{Spec} A \to \mathrm{base}\,p$ with $\mathrm{barPt}(A) \mathbin{;} \sigma_A = \mathrm{genPt}\,p$, a scheme $\Lambda.X \to \mathrm{base}\,p$ with a relative group law $\Lambda.L$, and parametrisations of $J_0(N_0)$. Let $\mathrm{pts}$ be a bijection from $J_0(N_0 p) = \mathrm{Pic}^0$ of the level-$N_0p$ modular function field over $\overline{\mathbb{Q}}$ onto the sections of $g$ over $\mathrm{genPt}\,p$, additive for $L$ and equivariant for $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ in the sense that $\mathrm{pts}(\sigma \cdot x)$ is $\operatorname{Spec}(\sigma)$ followed by $\mathrm{pts}(x)$. Assume given: a rank $t = \mathrm{toricRank}$ and a morphism $\mathrm{torusFibre}$ from the split torus $\mathbb{G}_{m,\kappa}^t$ into the base change of $g$ along $\mathrm{resPt}(A) \mathbin{;} \sigma_A$, which is a closed immersion and multiplicative on the $\kappa$-valued characters of $\kappa[\mathbb{Z}^t]$; two morphisms $\mathrm{abqFibre}\,i$ ($i \in \{0,1\}$) from that base change of $g$ to the corresponding base change of $\Lambda.f$ such that a point of the base change over any $T \to \operatorname{Spec}\kappa$ is killed by both exactly when it factors through $\mathrm{torusFibre}$, and which commute with precomposition by endomorphisms $\beta$ of the geometric special point; and $m > 0$ together with a morphism $\iota$ from $\mu_{m,A}^t = \operatorname{Spec} A[(\mathbb{Z}/m)^t]$ into the base change of $g$ along $\sigma_A$ which is multiplicative on $S$-valued characters for every $A$-algebra $S$ and whose reduction along $\mathrm{residue}\,A$, read in $G$, agrees with $\mathrm{torusFibre}$ restricted along $\mu_{m}^t \to \mathbb{G}_m^t$. For a character $\chi : A[(\mathbb{Z}/m)^t] \to \overline{\mathbb{Q}}$ of $A$-algebras, write $P_\chi \in J_0(N_0p)$ for the preimage under $\mathrm{pts}$ of the $\mathrm{genPt}\,p$-section obtained from $\mathrm{muPt}(A,t,m,\chi)$ followed by $\iota$. The conclusion is the conjunction of: (i) for every $\sigma$ in the inertia subgroup of $A$ inside $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and every $c \in \mathbb{N}$ with $\sigma\zeta = \zeta^c$ for all $\zeta$ with $\zeta^m = 1$, one has $\sigma \cdot P_\chi = c \cdot P_\chi$ for all $\chi$; and (ii) for every $\sigma$ in the decomposition subgroup of $A$ and every $\chi$ there is a character $\chi'$ with $\sigma \cdot P_\chi = P_{\chi'}$.
--
--   This is the statement that on the toric part of the special fibre inertia acts on the $m$-torsion points through the cyclotomic character, while the decomposition group merely permutes the toric characters; it is the pair of Galois clauses attached to a toric lift at level $m$. It is used by [`ModularCurve.JZeroNeronObjectAtP.exists_toricLift_of_torusFibre`](thm.html#ModularCurve.JZeroNeronObjectAtP.exists_toricLift_of_torusFibre), where the lift $\iota$ is produced by the henselian unique-lifting statement [`AlgebraicGeometry.SplitTorus.existsUnique_muLift_baseChange_of_torusFibre_of_henselian`](thm.html#AlgebraicGeometry.SplitTorus.existsUnique_muLift_baseChange_of_torusFibre_of_henselian).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_inertia_smul_eq_and_exists_decomposition_smul_eq_of_muLift.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.inertia_smul_eq_and_exists_decomposition_smul_eq_of_muLift
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
        GoodReductionJacobian.schemeHomOverComp β.1 β.2 (fibreMap (abqFibre i) x))

    (m : ℕ) (hm : 0 < m)
    (ι : SchemeHomOver (muStr ↥A toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA g))
    (hιmul : ∀ (S : Type) [CommRing S] [Algebra ↥A S] (χ χ' : WithConv (muCoord ↥A toricRank m →ₐ[↥A] S)),
      NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m (χ * χ').ofConv) ι =
        (L.baseChange Λ.σA).mul _
          (NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m χ.ofConv) ι)
          (NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m χ'.ofConv) ι))
    (hιsp : muBaseChange (residue ↥A) toricRank m ≫ ι.1 ≫ pullback.fst g Λ.σA =
      muToTorus (ResidueField ↥A) toricRank m ≫ torusFibre.1 ≫ pullback.fst g (resPt A ≫ Λ.σA)) :

    (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ m = 1 → σ ζ = ζ ^ c) →
        ∀ χ : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
          σ • pts.symm (genOfBaseChangePt Λ.hσA
              (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ) ι)) =
            c • pts.symm (genOfBaseChangePt Λ.hσA
              (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ) ι))) ∧

    (∀ σ ∈ A.decompositionSubgroup ℚ,
        ∀ χ : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
          ∃ χ' : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
            σ • pts.symm (genOfBaseChangePt Λ.hσA
                (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ) ι)) =
              pts.symm (genOfBaseChangePt Λ.hσA
                (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ') ι))) := by sorry
