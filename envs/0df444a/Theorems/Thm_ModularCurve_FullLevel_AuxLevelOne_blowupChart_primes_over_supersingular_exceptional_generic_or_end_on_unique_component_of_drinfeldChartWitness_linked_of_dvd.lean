-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_blowupChart_primes_over_supersingular_exceptional_generic_or_end_on_unique_component_of_drinfeldChartWitness_linked_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.blowupChart_primes_over_supersingular_exceptional_generic_or_end_on_unique_component_of_drinfeldChartWitness_linked_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/4f39dd2b-2385-54eb-8557-db8b63b38224
-- title:
--   Trichotomy and end classification on the blown-up supersingular chart
-- statement:
--   **Arithmetic data.** Fix a prime $q$ and a positive integer $M'$ with $q \nmid M'$, together with a prime $\ell$ satisfying $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic $0$ and $\zeta \in L$ a primitive $q$-th root of unity; the hypothesis `hι` provides a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = \exp(2\pi i/q)$. Let $H_1$ be a subgroup of $(\mathbb{Z}/q^2M')^\times$ which, by `hH₁`, is the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22) — the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$ — with the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell)^\times$ (using $\ell \mid q^2M'$); so $H_1$ consists of the units congruent to $1$ modulo $q$ and modulo $\ell$. Let $K$ be an intermediate field of $L \subseteq \mathrm{LaurentSeries}(L)$ which, by `hK`, equals [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁)`](def/ModularCurve_LaurentCoeff.html#L103): the subfield generated over $L$ by the coefficientwise image, under $\mathbb{Q} \to L$, of the $q$-expansion function field of $\Gamma_{H_1}(q^2M')$.
--
--   **Local base and chart.** Let $A$ be a discrete valuation domain with fraction field $L$, henselian local and with algebraically closed residue field, carrying compatible algebra structures over which $K$ is an $A$-algebra; assume $q \in \mathfrak{m}_A$ (`hAq`) and that $\zeta$ lies in the image of $A$ (`hζA`). Let $j \in K$ be nonzero whose Laurent series is, by `hj`, the coefficientwise image [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81) of the rational $q$-expansion of the modular $j$-function. Let $\varpi$ be a uniformiser of $A$ (`hϖ`: $\mathfrak{m}_A = (\varpi)$) and $\varpi_t \in A$ a tame constant, i.e. (`hϖt`) $\varpi_t^{\,q^2-1} = q u$ for some unit $u$ of $A$. Write $C :=$ `chartAlgFin A ↥K j` for the chart algebra, the $A$-subalgebra of elements of $K$ integral over $A[j]$, and let $y \subseteq C$ be a maximal ideal (`hy`) containing $\varpi$ (`hϖy`) which is supersingular in the sense of `hss`: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : C \to \Omega$ with kernel $y$, the value $\varphi(\mathrm{jChartFin}\,A\,↥K\,j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), that is, every elliptic Weierstrass curve over $\Omega$ with this $j$-invariant has no nonzero $q$-torsion point.
--
--   **The rigidity hypothesis `hArig`.** This hypothesis asserts, for every point $z$ of the two-chart integral model $X :=$ [`AlgebraicCurve.TwoChartIntegralModel A ↥K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) at which the germ of $\varpi$ lies in the maximal ideal of the stalk, and every point $y'$ of the affine chart `XFin` mapping to $z$ and satisfying the supersingularity condition above, the existence of a complete discrete valuation domain $W$, a homomorphism $\sigma : A \to W$ with $\mathfrak{m}_W = (\sigma\varpi)$, power series $f, u, v \in W[[X_0,X_1]]$ with $u, v$ units and $f \equiv$ [`DrinfeldCurve.LocalChart.drinfeldForm q W`](def/DrinfeldCurve_LocalChart.html#L18) $= X_0X_1^q - X_0^qX_1$ modulo $(X_0,X_1)^{q+2}$, and an isomorphism $e$ from the adic completion of the stalk at $z$ onto $S := W[[X_0,X_1]]/(C(\sigma(\varpi_t^{q+1}))v - fu)$, subject to a list of riders, summarised here: compatibility of $e$ with constants from $A$; stability of the chart algebra under the level automorphisms $\tau$ of $K$ attached to $\gamma^{-1}$ for $\gamma \in \Gamma_0(M')$ (the predicate [`ModularCurve.FullLevel.IsLevelAutAt`](def/ModularCurve_FullLevelLevelAutAt.html#L29), which says that $\tau$ realises, after reading coefficients through $\iota$, the weight-$k$ action of the matrix attached to $\gamma^{-1}$ and $q$ on quotients of $q$-expansions of modular forms of level $\Gamma_{H_1}(q^2M')$); congruence of such $\tau$ to the identity modulo $y'$ when $\gamma_{11} \equiv 1 \pmod{\ell}$; an equivariance clause producing for each such $\tau$ fixing $y'$ a ring automorphism $\theta$ of $S$, a constant $c \in W$ with $c^{q+1} \equiv 1$ and a matrix $M$ over $W$ with $M_{ij} \equiv c\,\gamma_{ij}$ modulo $\mathfrak{m}_W$, such that $\theta$ matches $\tau$ through $e$, fixes constants and sends $X_j$ to $\sum_i M_{ij}X_i$ modulo $(X_0,X_1)^2$, with $c \equiv 1$ when $\gamma_{11} \equiv 1 \pmod{\ell}$ and $c \not\equiv 1$ when $\gamma \in \Gamma(q)$ and $\tau \neq \mathrm{id}$; a separation clause saying that two primes of $S$ containing $\sigma\varpi$, not containing both coordinates, and having tangent directions $(a_1,b_1)$, $(a_2,b_2)$ with $a_1b_2 - a_2b_1$ not divisible by $q$ have distinct contractions to the stalk; an identification, for the branch with direction $(1,0)$, of membership in the contracted prime with the condition that all Laurent coefficients lie in $\mathfrak{m}_A$; and a branch clause on [`ModularCurve.jqNModC L q`](def/ModularCurve_JqCoeff.html#L18) (the $j$-expansion with $\mathsf{q}$ replaced by $\mathsf{q}^{q}$), which is required to lie in $C$, to be congruent modulo $y'$ to some $a_0 \in A$, and to have image under $e$ equal to the class of a power series $h \in (X_0,X_1)^{e_0}$, $e_0 \ge 1$, whose degree-$e_0$ form takes unit values at all $(a,b)$ not both in $\mathfrak{m}_W$ with $a^qb - ab^q \in \mathfrak{m}_W$.
--
--   **The chosen point and its witness.** Fixed are a point $z$ of $X$, the germ $\varpi_z$ of $\varpi$ at $z$ (`hϖz`) lying in the maximal ideal of the stalk (`hz`), a point $y'$ of `XFin` with `ιFin` image $z$ (`hy'`) satisfying the supersingularity condition `hss'`, and the identification `hy'y`: $y'$ corresponds to the ideal $y$. Fixed are furthermore a complete discrete valuation domain $W_1$, a homomorphism $\sigma_1 : A \to W_1$ with $\mathfrak{m}_{W_1} = (\sigma_1\varpi)$, power series $f_1, u_1, v_1$ with $u_1, v_1$ units (`hu₁`, `hv₁`) and $f_1$ congruent to the Drinfeld form modulo $(X_0,X_1)^{q+2}$ (`hf₁`), and an isomorphism $e_1$ from the adic completion of the stalk at $z$ onto $S := W_1[[X_0,X_1]]/(C(\sigma_1(\varpi_t^{q+1}))v_1 - f_1u_1)$; the hypothesis `hW₁` requires of this particular witness exactly the list of riders described above (constants, stability, congruence modulo $y'$, equivariance with $\theta$, $c$, $M$, separation of tangent directions, the branch criterion in terms of Laurent coefficients, and the clause on [`ModularCurve.jqNModC L q`](def/ModularCurve_JqCoeff.html#L18)).
--
--   **Centre, blow-up chart and valuation ring.** Let $J$ be an ideal of $C$ which, by `hJ`, is the infimum of the set of ideals obtained as follows: for $\gamma \in \Gamma(q) \cap \Gamma_0(M')$ and $\tau$ a level automorphism attached to $\gamma^{-1}$ preserving $C$, take the contraction along the composite $C \to \mathcal{O}_{X,z} \to \widehat{\mathcal{O}}_{X,z} \xrightarrow{e_1} S$ of the ideal of $S$ generated by the classes of $C(\sigma_1\varpi_t)$, $X_0$ and $X_1$, and pull it back along the restriction of $\tau$ to $C$. Let $B$ be the $A$-subalgebra of $K$ which, by `hB`, is generated over $C$ by $\{x \in K : x\varpi_t \in J\}$, and let $W$ be a valuation subring of $K$ containing $B$ (`hBW`). Four further hypothesis blocks are imposed: `hR1` — $C \subseteq B$ and $B$ has fraction field $K$; `hR2` — $B$ is formally smooth and of finite presentation over $A$, and $B/\varpi B$ has Krull dimension at most $1$; `hR3` (five clauses) — an element of $L$ lies in $W$ exactly when it comes from $A$, $\mathfrak{m}_W$ is generated by $\varpi$, $W$ is a discrete valuation ring, an element of $C$ lies in $y$ exactly when it lies in $\mathfrak{m}_W$, and $W$ is the localisation of $B$ at the contraction of $\mathfrak{m}_W$; and `hEQ` (five clauses) — for every $\mathbb{F}_{q^2}$-algebra structure on the residue field $k$ of $A$ there is a surjection $\rho : B \to$ [`DrinfeldCurve.CoordRing q k`](def/DrinfeldCurve_CoordRing.html#L21) with kernel the elements lying in $\mathfrak{m}_W$, compatible with the residue map of $A$, and equivariant for level automorphisms preserving $W$ in the sense that each $\gamma \in \Gamma_0(M')$ and attached $\tau$ come with $c \in \mathbb{F}_{q^2}^\times$ such that $(\mathrm{redQ}(\gamma), c)$ lies in [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276) and $\rho \circ \tau$ equals [`DrinfeldCurve.hAction`](def/DrinfeldCurve_CoordRing.html#L325) of this pair composed with $\rho$, with $c \neq 1$ when $\gamma \in \Gamma(q)$ and $\tau \neq \mathrm{id}$; $B$ is stable under all level automorphisms with $\gamma \in \Gamma_0(M')$; every prime of $B$ containing $\varpi$ is the image of $\mathfrak{m}_W$ under some level automorphism with $\gamma \in \Gamma(q) \cap \Gamma_0(M')$; an element of $B$ all of whose such translates lie in $\mathfrak{m}_W$ is divisible by $\varpi$; and a level automorphism preserving $y$ preserves $W$.
--
--   **Conclusion.** For $a \in C$ nonzero write $B_a$ for the $A$-subalgebra of $K$ generated over $C$ by $\{x \in K : xa \in J\}$. Call a subring $O \subseteq K$ an *end* if there are $a \in J$ with $a \neq 0$ in $K$ and a maximal ideal $P$ of $B_a$ such that $O$ is the localisation of $B_a$ at $P$ inside $K$ (an $f \in K$ lies in $O$ exactly when $f = g/h$ with $g, h \in B_a$, $h \notin P$), no element of $y$ which lies in $O$ is a unit of $O$, and $B \not\subseteq O$. For a prime $\mathfrak{p}$ of $C$ say that a prime $\mathfrak{q}$ of $O$ *marks* $\mathfrak{p}$ if $\varpi \in \mathfrak{q}$ whenever $\varpi \in O$, some element of $y$ lying in $O$ is outside $\mathfrak{q}$, and for every $c \in C$ lying in $O$ one has $c \in \mathfrak{p}$ if and only if $c \in \mathfrak{q}$. Finally, call $\mathfrak{p}$ *admissible* if it is prime, contains $\varpi$, and satisfies $\mathfrak{p} \subseteq y$, $\mathfrak{p} \neq y$.
--
--   The assertion is the conjunction of the following five statements.
--
--   (i) (Trichotomy.) For every nonzero $a \in J$ and every prime $Q$ of $B_a$ containing $\varpi$ whose contraction to $C$ is contained in $y$: either $Q$ is maximal, or the localisation of $B_a$ at $Q$ contains $B$ (every $f \in B$ is $g/h$ with $g, h \in B_a$, $h \notin Q$), or some element of $y$ has image in $B_a$ outside $Q$.
--
--   (ii) (Each end marks an admissible prime.) For every end $O$ there is an admissible prime $\mathfrak{p}$ of $C$ and a prime $\mathfrak{q}$ of $O$ marking $\mathfrak{p}$.
--
--   (iii) (Uniqueness of the prime.) For every end $O$ and all admissible primes $\mathfrak{p}, \mathfrak{p}'$ of $C$, if some prime of $O$ marks $\mathfrak{p}$ and some prime of $O$ marks $\mathfrak{p}'$, then $\mathfrak{p} = \mathfrak{p}'$.
--
--   (iv) (Every admissible prime is attained.) For every admissible prime $\mathfrak{p}$ of $C$ there is an end $O$ together with a prime of $O$ marking $\mathfrak{p}$.
--
--   (v) (Uniqueness of the end.) For all ends $O, O'$ and every admissible prime $\mathfrak{p}$ of $C$, if some prime of $O$ marks $\mathfrak{p}$ and some prime of $O'$ marks $\mathfrak{p}$, then $O = O'$.
--
--   Together, (ii)–(v) state that the ends of the blow-up of the chart $C$ along the orbit centre $J$ are in bijection with the primes of $C$ that contain $\varpi$ and lie strictly below the supersingular maximal ideal $y$.
--
--   This is the local analysis of the exceptional fibre of the blow-up, at the orbit centre $J$, of the supersingular chart of the two-chart integral model: primes of a blow-up chart over $y$ are either closed points, or dominated by the distinguished chart $B$, or miss the centre, and the remaining 'ends' correspond one-to-one with the primes of the chart algebra lying strictly under $y$ over the uniformiser. It feeds the localisation and valuative-cover statements for the ends of the blown-up chart in the level-one auxiliary construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_blowupChart_primes_over_supersingular_exceptional_generic_or_end_on_unique_component_of_drinfeldChartWitness_linked_of_dvd.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevelOne.blowupChart_primes_over_supersingular_exceptional_generic_or_end_on_unique_component_of_drinfeldChartWitness_linked_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})

    (ϖt : A) (hϖt : ∃ u : A, IsUnit u ∧ ϖt ^ (q ^ 2 - 1) = (q : A) * u)

    (y : Ideal ↥(chartAlgFin A (↥K) j)) (hy : y.IsMaximal) (hϖy : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω), RingHom.ker φ = y → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (hArig : ∀ (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω),
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : A →+* W)
        (_ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
        (f u v : MvPowerSeries (Fin 2) W) (_ : IsUnit u) (_ : IsUnit v)
        (_ : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
        (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u}),

        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
        let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓ) = 1 →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W) (M : Matrix (Fin 2) (Fin 2) W),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e (toC (germY a))) = e (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W) ∈ IsLocalRing.maximalIdeal W) ∧
                  (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L q ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W, (a ∉ IsLocalRing.maximalIdeal W ∨ b ∉ IsLocalRing.maximalIdeal W) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (hy'y : y'.asIdeal = y)
      (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁]
        [IsAdicComplete (IsLocalRing.maximalIdeal W₁) W₁] (σ₁ : A →+* W₁)
        (hσ₁ : IsLocalRing.maximalIdeal W₁ = Ideal.span {σ₁ ϖ})
        (f₁ u₁ v₁ : MvPowerSeries (Fin 2) W₁) (hu₁ : IsUnit u₁) (hv₁ : IsUnit v₁)
        (hf₁ : f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁ ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ (q + 2))
        (e₁ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})

    (hW₁ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e₁ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ₁ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓ) = 1 →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W₁) (M : Matrix (Fin 2) (Fin 2) W₁),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e₁ (toC (germY a))) = e₁ (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W₁, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W₁) ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W₁)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e₁ : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e₁ : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₁) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e₁ : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L q ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W₁)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W₁, (a ∉ IsLocalRing.maximalIdeal W₁ ∨ b ∉ IsLocalRing.maximalIdeal W₁) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W₁ →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e₁ : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (J : Ideal ↥(chartAlgFin A (↥K) j))
    (hJ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
        J = sInf {J' : Ideal ↥(chartAlgFin A (↥K) j) | ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q)
          (_ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
          (_ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ)
          (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
          J' = Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres)
            (Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY))
              (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}))})

    (B : Subalgebra A ↥K)
    (hB : B = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A)

    (W : ValuationSubring ↥K) (hBW : ∀ f : ↥K, f ∈ B → f ∈ W)
    (hR1 :

      chartAlgFin A (↥K) j ≤ B ∧
      (∀ f : ↥K, ∃ g h : ↥B, (h : ↥K) ≠ 0 ∧ f * (h : ↥K) = (g : ↥K)))
    (hR2 :

      Algebra.FormallySmooth A ↥B ∧ Algebra.FinitePresentation A ↥B ∧
      Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {algebraMap A ↥B ϖ}))
    (hR3 :

      (∀ x : L, algebraMap L ↥K x ∈ W ↔ ∃ a : A, algebraMap A L a = x) ∧
      maximalIdeal ↥W = Ideal.span {(⟨algebraMap A ↥K ϖ, hBW _ (B.algebraMap_mem ϖ)⟩ : ↥W)} ∧
      IsDiscreteValuationRing ↥W ∧
      (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y ↔
        ∃ hb : (b : ↥K) ∈ W, (⟨(b : ↥K), hb⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
      (∀ f : ↥K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : ↥K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : ↥K) = (g : ↥K)))
    (hEQ :

      (∀ (inst : Algebra (GaloisField q 2) (ResidueField A)),
        ∃ (ρ : ↥B →+* DrinfeldCurve.CoordRing q (ResidueField A)),
          Function.Surjective ρ ∧
          (∀ b : ↥B, ρ b = 0 ↔ (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
          (∀ a : A, ρ (algebraMap A ↥B a) = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (residue A a)) ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
              (∀ f : ↥K, f ∈ W ↔ τ f ∈ W) →
              ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                (∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B), ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b)) ∧
                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c ≠ 1))) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ f : ↥K, f ∈ B → τ f ∈ B) ∧
      (∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
        ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
          ∃ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ ∧
            ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → τ (b : ↥K) ∈ B ∧ ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hb⟩ : ↥B) ∈ Q) ∧
      (∀ b : ↥B, (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hBW _ hb⟩ : ↥W) ∈ maximalIdeal ↥W) →
        algebraMap A ↥B ϖ ∣ b) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
              b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
          ∀ f : ↥K, f ∈ W ↔ τ f ∈ W))
    :

      (∀ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
        let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
            {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
        ∀ Q : Ideal ↥Ba, Q.IsPrime → algebraMap A ↥Ba ϖ ∈ Q →
          (∀ (c : ↥(chartAlgFin A (↥K) j)) (hc : ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ Ba), (⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hc⟩ : ↥Ba) ∈ Q → c ∈ y) →
            Q.IsMaximal ∨
            (∀ f : ↥K, f ∈ B → ∃ g h : ↥Ba, h ∉ Q ∧ f * (h : ↥K) = (g : ↥K)) ∨
            (∃ b : ↥(chartAlgFin A (↥K) j), b ∈ y ∧ ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ Ba, (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥Ba) ∉ Q)) ∧

      (∀ O : Subring ↥K, (∃ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
          let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
            {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
          ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
            (∀ f : ↥K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) ∧
            (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
              ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O)) ∧
            ¬ (∀ f : ↥K, f ∈ B → f ∈ O)) →
        ∃ 𝔭 : Ideal ↥(chartAlgFin A (↥K) j), (𝔭.IsPrime ∧ algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ 𝔭 ∧ 𝔭 ≤ y ∧ 𝔭 ≠ y) ∧ (∃ 𝔮 : Ideal ↥O, 𝔮.IsPrime ∧
            (∀ h : algebraMap A ↥K ϖ ∈ O, (⟨algebraMap A ↥K ϖ, h⟩ : ↥O) ∈ 𝔮) ∧
            (∃ b : ↥(chartAlgFin A (↥K) j), b ∈ y ∧ ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O) ∉ 𝔮) ∧
            (∀ (c : ↥(chartAlgFin A (↥K) j)) (hc : ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O),
              c ∈ 𝔭 ↔ (⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hc⟩ : ↥O) ∈ 𝔮))) ∧

      (∀ O : Subring ↥K, (∃ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
          let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
            {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
          ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
            (∀ f : ↥K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) ∧
            (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
              ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O)) ∧
            ¬ (∀ f : ↥K, f ∈ B → f ∈ O)) →
        ∀ 𝔭 𝔭' : Ideal ↥(chartAlgFin A (↥K) j), (𝔭.IsPrime ∧ algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ 𝔭 ∧ 𝔭 ≤ y ∧ 𝔭 ≠ y) → (𝔭'.IsPrime ∧ algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ 𝔭' ∧ 𝔭' ≤ y ∧ 𝔭' ≠ y) → (∃ 𝔮 : Ideal ↥O, 𝔮.IsPrime ∧
            (∀ h : algebraMap A ↥K ϖ ∈ O, (⟨algebraMap A ↥K ϖ, h⟩ : ↥O) ∈ 𝔮) ∧
            (∃ b : ↥(chartAlgFin A (↥K) j), b ∈ y ∧ ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O) ∉ 𝔮) ∧
            (∀ (c : ↥(chartAlgFin A (↥K) j)) (hc : ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O),
              c ∈ 𝔭 ↔ (⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hc⟩ : ↥O) ∈ 𝔮)) → (∃ 𝔮 : Ideal ↥O, 𝔮.IsPrime ∧
            (∀ h : algebraMap A ↥K ϖ ∈ O, (⟨algebraMap A ↥K ϖ, h⟩ : ↥O) ∈ 𝔮) ∧
            (∃ b : ↥(chartAlgFin A (↥K) j), b ∈ y ∧ ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O) ∉ 𝔮) ∧
            (∀ (c : ↥(chartAlgFin A (↥K) j)) (hc : ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O),
              c ∈ 𝔭' ↔ (⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hc⟩ : ↥O) ∈ 𝔮)) → 𝔭 = 𝔭') ∧

      (∀ 𝔭 : Ideal ↥(chartAlgFin A (↥K) j), (𝔭.IsPrime ∧ algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ 𝔭 ∧ 𝔭 ≤ y ∧ 𝔭 ≠ y) →
        ∃ O : Subring ↥K, (∃ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
          let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
            {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
          ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
            (∀ f : ↥K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) ∧
            (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
              ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O)) ∧
            ¬ (∀ f : ↥K, f ∈ B → f ∈ O)) ∧ (∃ 𝔮 : Ideal ↥O, 𝔮.IsPrime ∧
            (∀ h : algebraMap A ↥K ϖ ∈ O, (⟨algebraMap A ↥K ϖ, h⟩ : ↥O) ∈ 𝔮) ∧
            (∃ b : ↥(chartAlgFin A (↥K) j), b ∈ y ∧ ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O) ∉ 𝔮) ∧
            (∀ (c : ↥(chartAlgFin A (↥K) j)) (hc : ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O),
              c ∈ 𝔭 ↔ (⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hc⟩ : ↥O) ∈ 𝔮))) ∧

      (∀ O O' : Subring ↥K, (∃ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
          let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
            {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
          ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
            (∀ f : ↥K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) ∧
            (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
              ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O)) ∧
            ¬ (∀ f : ↥K, f ∈ B → f ∈ O)) → (∃ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
          let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
            {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
          ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
            (∀ f : ↥K, f ∈ O' ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) ∧
            (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
              ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O', ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O')) ∧
            ¬ (∀ f : ↥K, f ∈ B → f ∈ O')) →
        ∀ 𝔭 : Ideal ↥(chartAlgFin A (↥K) j), (𝔭.IsPrime ∧ algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ 𝔭 ∧ 𝔭 ≤ y ∧ 𝔭 ≠ y) → (∃ 𝔮 : Ideal ↥O, 𝔮.IsPrime ∧
            (∀ h : algebraMap A ↥K ϖ ∈ O, (⟨algebraMap A ↥K ϖ, h⟩ : ↥O) ∈ 𝔮) ∧
            (∃ b : ↥(chartAlgFin A (↥K) j), b ∈ y ∧ ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O) ∉ 𝔮) ∧
            (∀ (c : ↥(chartAlgFin A (↥K) j)) (hc : ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O),
              c ∈ 𝔭 ↔ (⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hc⟩ : ↥O) ∈ 𝔮)) → (∃ 𝔮 : Ideal ↥O', 𝔮.IsPrime ∧
            (∀ h : algebraMap A ↥K ϖ ∈ O', (⟨algebraMap A ↥K ϖ, h⟩ : ↥O') ∈ 𝔮) ∧
            (∃ b : ↥(chartAlgFin A (↥K) j), b ∈ y ∧ ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O', (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O') ∉ 𝔮) ∧
            (∀ (c : ↥(chartAlgFin A (↥K) j)) (hc : ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O'),
              c ∈ 𝔭 ↔ (⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hc⟩ : ↥O') ∈ 𝔮)) → O = O') := by sorry
