-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_inertia_smul_eq_and_exists_decomposition_smul_eq_of_muLift
-- name    : ModularCurve.JHNeronObjectAtP.inertia_smul_eq_and_exists_decomposition_smul_eq_of_muLift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/a0192881-df4f-5584-b25d-a818d2c2eacf
-- title:
--   Galois action on toric points of a μ_m^t-lift
-- statement:
--   Fix a prime $p$, an integer $M\neq 0$ with $p\mid M$ and a subgroup $H\le(\mathbf Z/M)^\times$. Let $g:G\to\operatorname{Spec}\mathbf Z_{(p)}$ be smooth, separated and quasi-compact (the base ring being the rationals with denominator coprime to $p$), and let $L$ be a commutative relative group law on $g$ all of whose multiplication morphisms `L.schemeNsmul n`, $n>0$, are flat and locally quasi-finite. Let $A$ be a valuation subring of an algebraic closure of $\mathbf Q$, with residue field $\kappa$, and $\Lambda$ a `LevelData p M H hpM A`, of which the structure morphism $\sigma_A:\operatorname{Spec}A\to\operatorname{Spec}\mathbf Z_{(p)}$, the identification $h_{\sigma_A}$ of its geometric generic point with `genPt p`, the scheme $\Lambda.f$ and its group law $\Lambda.L$ occur. Let $\mathrm{pts}$ be a bijection from $\mathrm{Pic}^0$ of the function field of $X_H(M)$ over $\overline{\mathbf Q}$ onto the sections of $g$ over `genPt p`, additive for $L$ and equivariant for $\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q)$ acting on sections by composition with $\operatorname{Spec}\sigma$. Assume given a rank $t$, a closed immersion $\tau$ of the split torus $\mathbf G_m^t$ over $\kappa$ into the base change of $g$ along `resPt A ≫ Λ.σA`, multiplicative on $\kappa$-valued characters; two morphisms $\mathrm{abq}_i$ ($i\in\{0,1\}$) from that base change to the base change of $\Lambda.f$, such that a point $x$ over any $s:T\to\operatorname{Spec}\kappa$ has both composites with $\mathrm{abq}_i$ equal to the identity section of the base change of $\Lambda.L$ exactly when $x$ factors through $\tau$, and such that the induced fibre maps commute with twisting by endomorphisms $\beta$ of the special point; and, for some $m>0$, a section $\iota$ of the base change of $g$ along $\sigma_A$ parametrised by $\mu_m^t$ over $A$, multiplicative on $S$-valued characters for every $A$-algebra $S$, whose reduction along $\operatorname{res}:A\to\kappa$ agrees with the restriction of $\tau$ to $\mu_m^t$. For a character $\chi$ of $A[(\mathbf Z/m)^t]$ with values in $\overline{\mathbf Q}$, write $P_\chi\in\mathrm{Pic}^0$ for the element whose associated $\overline{\mathbf Q}$-section is obtained by composing the point $\chi$ of $\mu_m^t$ with $\iota$ and transporting along $h_{\sigma_A}$. The conclusion is twofold: first, for every $\sigma$ in the image of the inertia subgroup of $A$ over $\mathbf Q$ inside the decomposition subgroup, every $c\in\mathbf N$ with $\sigma\zeta=\zeta^c$ for all $\zeta\in\overline{\mathbf Q}$ with $\zeta^m=1$, and every $\chi$, one has $\sigma\cdot P_\chi=c\,P_\chi$; second, for every $\sigma$ in the decomposition subgroup of $A$ over $\mathbf Q$ and every $\chi$ there is a character $\chi'$ with $\sigma\cdot P_\chi=P_{\chi'}$.
--
--   This describes the Galois action on the $\mu_m^t$-torsion points coming from the toric part of a semistable reduction: inertia at the place $A$ acts through the cyclotomic character, and the decomposition group permutes the toric points. It is the level-$\Gamma_H(M)$ form of the statement and is used by [`ModularCurve.JHNeronObjectAtP.exists_toricLift_of_torusFibre`](thm.html#ModularCurve.JHNeronObjectAtP.exists_toricLift_of_torusFibre) in the construction of the toric lift over the henselian valuation ring $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_inertia_smul_eq_and_exists_decomposition_smul_eq_of_muLift.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
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

theorem ModularCurve.JHNeronObjectAtP.inertia_smul_eq_and_exists_decomposition_smul_eq_of_muLift
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
