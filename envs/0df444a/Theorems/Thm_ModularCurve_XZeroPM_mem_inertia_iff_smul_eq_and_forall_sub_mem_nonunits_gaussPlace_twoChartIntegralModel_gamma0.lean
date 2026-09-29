-- Prove2me | Theorems.Thm_ModularCurve_XZeroPM_mem_inertia_iff_smul_eq_and_forall_sub_mem_nonunits_gaussPlace_twoChartIntegralModel_gamma0
-- name    : ModularCurve.XZeroPM.mem_inertia_iff_smul_eq_and_forall_sub_mem_nonunits_gaussPlace_twoChartIntegralModel_gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/64838e49-f4b9-5d50-8dda-a8a30ab6b4d0
-- title:
--   Inertia at a supersingular chart point via the Gauss place
-- statement:
--   Fix a prime $p$ and $M \ge 5$ with $p \nmid M$, a field $L$ of characteristic zero that is a $p$-cyclotomic extension of $\mathbb{Q}$ with primitive $p$-th root of unity $\zeta$, and inside $\mathrm{LaurentSeries}\,L$ the intermediate fields $K_1$, generated over $L$ by the coefficientwise image of the field of $q$-expansion ratios of integral modular forms for $\Gamma_1(M) \cap \Gamma_0(p)$, and $K_2$, generated likewise from $\Gamma_0(Mp)$, with $K_2 \le K_1$. Further data, all hypothesised and summarised here in groups: a discrete valuation ring $A$ with fraction field $L$ containing $p$ in its maximal ideal and $\zeta$ in its image, with uniformiser $\varpi$ and compatible algebra structures on $K_1,K_2$; elements $j \in K_1$, $j_2 \in K_2$, both nonzero, whose Laurent series is the image of the classical $j$-expansion $q^{-1}(1+\dots)$; a finite morphism $\pi_2$ of two-chart integral models over $A$ together with a finite $A$-algebra map $\iota_{F_2}$ of finite-chart rings (elements of $K_i$ integral over $A[j]$, resp. $A[j_2]$) compatible with $\pi_2$, the chart immersions and the structure maps to $\operatorname{Spec} A$, and with $\mathrm{chartAlgFin}\,A\,K_1\,j$ the integral closure of the image of $\iota_{F_2}$; a point $z$ of the model at which the germ of $\varpi$ lies in the maximal ideal of the stalk, a point $y$ of the finite chart above $z$ whose ideal $\mathfrak{y}$ is supersingular, in the sense that for every algebraically closed field $\Omega$ of characteristic $p$ and every ring map $\varphi$ from the finite-chart ring to $\Omega$ with kernel $\mathfrak{y}$, $\varphi(j)$ lies in $\mathrm{ssJSet}\,p\,\Omega$, the set of $j$-invariants all of whose elliptic curves have no nontrivial $p$-torsion point; a finite group $G$ acting faithfully on $K_1$ by semiring automorphisms with fixed field exactly $K_2$, acting compatibly on the finite-chart ring; the contraction $\mathfrak{y}_2$ of $\mathfrak{y}$ along $\iota_{F_2}$; an algebraically closed field $k$ of characteristic $p$, a supersingular place $w$ of $\mathrm{modularFunctionFieldC}\,k\,M$ (rational, affine geometric, with $\mathrm{jGeomGen}$ evaluating into $\mathrm{ssJSet}\,p\,k$), and a ring map $\rho$ from the level-$\Gamma_0(Mp)$ chart ring onto a subring generating that function field, killing $\varpi$, sending the chart coordinate to $\mathrm{jGeomGen}$, landing in the valuation ring of $w$ and pulling its nonunits back to $\mathfrak{y}_2$; the Gauss valuation subring $W_0$ of $K_1$, consisting of the ratios of images of power series over $A$ with denominator of nonzero reduction, which contains the finite-chart ring, is $G$-stable, and whose nonunits meet the chart inside $\mathfrak{y}$, while some element of $\mathfrak{y}$ is a unit of $W_0$; and a valuation subring $P$ of the residue field of $W_0$ containing all residues of chart elements, with nonunits cutting out exactly $\mathfrak{y}$, uniquely determined by these two properties, and such that every element of $P$ is congruent to the residue of a chart element modulo the nonunits of $P$, the $G$-action on the residue field of $W_0$ being induced by that on $W_0$. The conclusion is that for $g \in G$, $g$ lies in the inertia subgroup $\mathfrak{y}.\mathrm{inertia}\,G$ if and only if $g \bullet P = P$ and $g \bullet e - e$ is a nonunit of $P$ for every $e \in P$.
--
--   This identifies the inertia subgroup, for the $G$-action on the $j$-finite chart ring, of a supersingular point of the integral model of $X(\Gamma_1(M) \cap \Gamma_0(p))$ with the inertia subgroup of the associated place $P$ of the residue field of the Gauss valuation ring of the function field. It feeds the comparison of the order of this inertia group with the width of the corresponding place in the special fibre, a step in the local analysis of $X_0(Mp)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XZeroPM_mem_inertia_iff_smul_eq_and_forall_sub_mem_nonunits_gaussPlace_twoChartIntegralModel_gamma0.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_PlaceWidthChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

theorem ModularCurve.XZeroPM.mem_inertia_iff_smul_eq_and_forall_sub_mem_nonunits_gaussPlace_twoChartIntegralModel_gamma0
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))

    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (hle : K₂ ≤ K₁)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    [Algebra A ↥K₂] [IsScalarTower A L ↥K₂]
    (j : ↥K₁) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (j₂ : ↥K₂) (hj₂ : ((j₂ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₂ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (π₂ : (AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j) ⟶ (AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂))
    (ιF₂ : ↥(chartAlgFin A (↥K₂) j₂) →ₐ[A] ↥(chartAlgFin A (↥K₁) j))
    (hιF₂ : ∀ x, (((ιF₂ x : ↥K₁) : LaurentSeries L)) = ((x : ↥K₂) : LaurentSeries L))
    (hπbase : π₂ ≫ toBase A (↥K₂) j₂ = toBase A (↥K₁) j)
    (hπF : Spec.map (CommRingCat.ofHom ιF₂.toRingHom) ≫ ιFin A (↥K₂) j₂ = ιFin A (↥K₁) j ≫ π₂)
    (hpreF : π₂ ⁻¹ᵁ (ιFin A (↥K₂) j₂).opensRange = (ιFin A (↥K₁) j).opensRange)
    (hπfin : IsFinite π₂) (hιF₂fin : ιF₂.toRingHom.Finite)
    (hintF : ∀ x : ↥K₁, x ∈ chartAlgFin A (↥K₁) j ↔ IsIntegral ↥((ιF₂.range).map (chartAlgFin A (↥K₁) j).val) x)

    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j).presheaf.stalk z)
    (hϖz : ϖz = (((AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j).presheaf.germ ⊤ z trivial).hom (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₁) j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ))))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j).presheaf.stalk z))
    (y : ↥(XFin A (↥K₁) j)) (hy : (ιFin A (↥K₁) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K₁) j) →+* Ω),
      RingHom.ker φ = y.asIdeal → φ (jChartFin A (↥K₁) j) ∈ ModularCurve.ssJSet p Ω)

    (G : Type) [Group G] [Fintype G] [MulSemiringAction G ↥K₁] [FaithfulSMul G ↥K₁]
    (hGfixK : ∀ (g : G) (x : ↥K₁), (x : LaurentSeries L) ∈ K₂ → g • x = x)
    (hGinvK : ∀ x : ↥K₁, (∀ g : G, g • x = x) → (x : LaurentSeries L) ∈ K₂)
    [MulSemiringAction G ↥(chartAlgFin A (↥K₁) j)]
    (hGA : ∀ (g : G) (a : ↥(chartAlgFin A (↥K₁) j)), ((g • a : ↥(chartAlgFin A (↥K₁) j)) : ↥K₁) = g • (a : ↥K₁))

    (𝔶 : Ideal ↥(chartAlgFin A (↥K₁) j)) (h𝔶 : 𝔶 = y.asIdeal)

    (𝔶₂ : Ideal ↥(chartAlgFin A (↥K₂) j₂)) (h𝔶₂ : 𝔶₂ = Ideal.comap ιF₂.toRingHom 𝔶)

    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] [DecidableEq k]

    (w : AlgebraicCurve.Place k ↥(ModularCurve.modularFunctionFieldC k M))
    (hw : w ∈ ModularCurve.ssPlaces p M k)

    (ρ : ↥(chartAlgFin A (↥K₂) j₂) →+* ↥(ModularCurve.modularFunctionFieldC k M))
    (hρϖ : ρ (algebraMap A ↥(chartAlgFin A (↥K₂) j₂) ϖ) = 0)
    (hρj : ρ (jChartFin A (↥K₂) j₂) = ModularCurve.jGeomGen k M)
    (hρint : ∀ b, ρ b ∈ w.toValuationSubring)
    (hρcent : ∀ b, ρ b ∈ w.toValuationSubring.nonunits ↔ b ∈ 𝔶₂)
    (hρbir : ∀ f : ↥(ModularCurve.modularFunctionFieldC k M), ∃ a b : ↥(Algebra.adjoin k (Set.range ρ)),
        (b : ↥(ModularCurve.modularFunctionFieldC k M)) ≠ 0 ∧ f * b = a)

    (W₀ : ValuationSubring ↥K₁)
    (hW₀ : ∀ f : ↥K₁, f ∈ W₀ ↔ ∃ x y' : PowerSeries A, y'.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y'.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hSW₀ : ∀ s : ↥(chartAlgFin A (↥K₁) j), (s : ↥K₁) ∈ W₀)
    (hyϖ : algebraMap A ↥(chartAlgFin A (↥K₁) j) ϖ ∈ y.asIdeal)
    (hy𝔓 : ∀ s : ↥(chartAlgFin A (↥K₁) j), (s : ↥K₁) ∈ W₀.nonunits → s ∈ y.asIdeal)
    (hy₀ : ∃ s : ↥(chartAlgFin A (↥K₁) j), s ∈ y.asIdeal ∧ (s : ↥K₁) ∉ W₀.nonunits)

    (hGW₀ : ∀ (g : G) (f : ↥K₁), f ∈ W₀ ↔ g • f ∈ W₀)

    (P : ValuationSubring (IsLocalRing.ResidueField ↥W₀))
    (hP : ∀ s : ↥(chartAlgFin A (↥K₁) j), IsLocalRing.residue ↥W₀ ⟨(s : ↥K₁), hSW₀ s⟩ ∈ P)
    (hPy : ∀ s : ↥(chartAlgFin A (↥K₁) j),
      IsLocalRing.residue ↥W₀ ⟨(s : ↥K₁), hSW₀ s⟩ ∈ P.nonunits ↔ s ∈ 𝔶)
    (huniq : ∀ P' : ValuationSubring (IsLocalRing.ResidueField ↥W₀),
      (∀ s : ↥(chartAlgFin A (↥K₁) j), IsLocalRing.residue ↥W₀ ⟨(s : ↥K₁), hSW₀ s⟩ ∈ P') →
      (∀ s : ↥(chartAlgFin A (↥K₁) j),
        IsLocalRing.residue ↥W₀ ⟨(s : ↥K₁), hSW₀ s⟩ ∈ P'.nonunits ↔ s ∈ 𝔶) → P' = P)
    (hres : ∀ e : ↥P, ∃ s : ↥(chartAlgFin A (↥K₁) j),
      (e : IsLocalRing.ResidueField ↥W₀) - IsLocalRing.residue ↥W₀ ⟨(s : ↥K₁), hSW₀ s⟩ ∈ P.nonunits)
    [MulSemiringAction G (IsLocalRing.ResidueField ↥W₀)]
    (hGres : ∀ (g : G) (f : ↥W₀), g • IsLocalRing.residue ↥W₀ f =
      IsLocalRing.residue ↥W₀ ⟨g • (f : ↥K₁), (hGW₀ g f).mp f.2⟩)
    (g : G) :
    g ∈ 𝔶.inertia G ↔
      (g • P = P ∧ ∀ e : ↥P, g • (e : IsLocalRing.ResidueField ↥W₀) - e ∈ P.nonunits) := by sorry
