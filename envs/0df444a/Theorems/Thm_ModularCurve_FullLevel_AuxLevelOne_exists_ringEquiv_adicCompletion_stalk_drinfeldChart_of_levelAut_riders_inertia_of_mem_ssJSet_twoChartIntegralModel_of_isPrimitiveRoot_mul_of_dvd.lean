-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_ringEquiv_adicCompletion_stalk_drinfeldChart_of_levelAut_riders_inertia_of_mem_ssJSet_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.exists_ringEquiv_adicCompletion_stalk_drinfeldChart_of_levelAut_riders_inertia_of_mem_ssJSet_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/9b4766b0-58c1-5da9-9591-7f10f6018c47
-- title:
--   Drinfeld local chart with level, branch and inertia equivariance
-- statement:
--   Fix a prime $q$ and a natural number $M'$, nonzero, with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, let $\zeta \in L$ be a primitive $q$-th root of unity and $\xi \in L$ a primitive $(q\ell)$-th root of unity with $\zeta = \xi^{\ell}$. Let $H_1 \le (\mathbb{Z}/q^2M')^{\times}$ be the subgroup `levelH q M'` $\cap\ \ker\big((\mathbb{Z}/q^2M')^{\times} \to (\mathbb{Z}/\ell)^{\times}\big)$, where `levelH q M'` is the kernel of the reduction $(\mathbb{Z}/q^2M')^{\times} \to (\mathbb{Z}/q)^{\times}$; thus $H_1$ consists of the units congruent to $1$ modulo $q$ and modulo $\ell$. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained as `laurentBaseChange`, i.e. the field generated over $L$ by the image, under coefficientwise extension of scalars $\mathbb{Q} \to L$, of the $q$-expansion function field `xHFunctionField (q ^ 2 * M') H₁` attached to the congruence subgroup $\Gamma_{H_1}(q^2M')$.
--
--   Let $A$ be a discrete valuation ring which is a domain with fraction field $L$, such that $q$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A$ in $L$, and let $K$ be an $A$-algebra compatibly with $L$. Let $j \in K$ be the element whose Laurent series is the $q$-expansion `jq` of the modular $j$-function, with $j \neq 0$, and let $\varpi$ be a uniformiser of $A$, so that the maximal ideal of $A$ is $(\varpi)$.
--
--   Let $X =$ `TwoChartIntegralModel A K j` be the two-chart integral model: the pushout of the two maps from the middle chart to $\mathrm{Spec}$ of the two subalgebras `chartAlgFin` and `chartAlgInf` of $K$, consisting of the elements of $K$ integral over $A[j]$, respectively over $A[j^{-1}]$. Let $z$ be a point of $X$, let $\varpi_z$ be the germ at $z$ of the global section of $X$ obtained by pulling back $\varpi$ along the structure morphism `toBase` to $\mathrm{Spec}\,A$, and assume $\varpi_z$ lies in the maximal ideal of the stalk $\mathcal{O}_{X,z}$, so that $z$ lies over the closed point of $\mathrm{Spec}\,A$. Let $y$ be a point of `XFin` $= \mathrm{Spec}(\,$`chartAlgFin A K j`$\,)$ whose image under the canonical morphism `ιFin` is $z$. The supersingularity hypothesis `hss` requires: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from `chartAlgFin A K j` to $\Omega$ with kernel the prime $y$, the value $\varphi(j)$ lies in `ssJSet q Ω`, i.e. every elliptic curve over $\Omega$ with $j$-invariant $\varphi(j)$ has no nonzero point killed by $q$.
--
--   Under these hypotheses there exist: a complete discrete valuation ring $W$ (a domain, discrete valuation ring, adically complete for its maximal ideal), a ring homomorphism $\sigma : A \to W$ with maximal ideal of $W$ equal to $(\sigma\varpi)$, power series $f, u, v \in W[[X_0,X_1]]$ with $u$ and $v$ units and
--   $$f - (X_0X_1^{q} - X_0^{q}X_1) \in (X_0,X_1)^{q+2},$$
--   and a ring isomorphism
--   $$e : \widehat{\mathcal{O}_{X,z}} \;\xrightarrow{\ \sim\ }\; S := W[[X_0,X_1]]\big/\big(C(\sigma\varpi)\,v - f\,u\big),$$
--   where $\widehat{\mathcal{O}_{X,z}}$ is the adic completion of the stalk $\mathcal{O}_{X,z}$ at its maximal ideal. Write `toC` for the canonical map $\mathcal{O}_{X,z} \to \widehat{\mathcal{O}_{X,z}}$, `mkS` for the quotient map $W[[X_0,X_1]] \to S$, and `germY` for the canonical ring homomorphism from `chartAlgFin A K j` to $\mathcal{O}_{X,z}$ through the chart `ιFin` at $y$. The isomorphism $e$ satisfies four further conditions.
--
--   (i) Constants: for every $a \in A$, the image in $S$ under $e$ of the germ at $z$ of the pullback of $a$ along `toBase` is `mkS` of the constant $C(\sigma a)$.
--
--   (ii) Equivariance for level automorphisms with linear parts. For every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M')$ and every $L$-algebra automorphism $\tau$ of $K$ satisfying `IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ` — that is: for all weights $k$, all modular forms $f_0, g_0$ of weight $k$ for $\Gamma_{H_1}(q^2M')$ with integral $q$-expansions $p_f, p_g$, with the series attached to $p_g$ nonzero, all $x \in K$ whose Laurent series is the image of $p_f/p_g$, and every embedding $\iota : L \to \mathbb{C}$ with $\iota\zeta = e^{2\pi i/q}$, the coefficientwise image under $\iota$ of $\tau x$ times the $q$-expansion of $g_0 \mid_k$ `conjElemN q γ⁻¹` equals the $q$-expansion of $f_0 \mid_k$ `conjElemN q γ⁻¹`, where `conjElemN q γ⁻¹` is the matrix $\begin{pmatrix} a & b/q \\ qc & d\end{pmatrix}$ for $\gamma^{-1} = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$ — and for every proof that $\tau$ preserves `chartAlgFin A K j`, if the induced endomorphism of the chart algebra is trivial modulo the prime $y$ (i.e. $\tau a - a \in y$ for all $a$ in the chart algebra), then there exist a ring automorphism $\theta$ of $S$, an element $c \in W$ and a matrix $M \in \mathrm{Mat}_{2\times 2}(W)$ such that: $\theta$ transports the image of the chart algebra in $S$ according to $\tau$, namely $\theta(e(\mathrm{toC}(\mathrm{germY}\,a))) = e(\mathrm{toC}(\mathrm{germY}(\tau a)))$ for all $a$ in the chart algebra; $\theta$ fixes every constant $C(w)$, $w \in W$; for each $j_0 \in \{0,1\}$, $\theta(X_{j_0}) - \sum_{i} C(M_{i j_0}) X_{i}$ lies in the square of the ideal of $S$ generated by the images of $X_0, X_1$, so that $M$ is the linear part of $\theta$; $c^{q+1} - 1$ lies in the maximal ideal of $W$; $M_{ij} \equiv c\,\gamma_{ij}$ modulo the maximal ideal of $W$ for all $i,j$; if $\gamma_{11} \equiv 1 \pmod{\ell}$ then $c \equiv 1$ modulo the maximal ideal of $W$; and if $\gamma \in \Gamma(q)$ and $\tau$ is not the identity on $K$, then $c - 1$ does not lie in the maximal ideal of $W$.
--
--   (iii) Anchoring of a branch. For every prime ideal $P$ of $S$ such that at least one of the images of $X_0$ and $X_1$ is not in $P$, such that the image of $C(\sigma\varpi)$ lies in $P$, and such that $P$ contains an element of the form $C(1)X_0 + C(0)X_1 + h$ with $h \in (X_0,X_1)^2$ (an element with linear part $X_0$), the following holds for every $a$ in `chartAlgFin A K j`: the image $\mathrm{toC}(\mathrm{germY}\,a)$ lies in the preimage of $P$ under $e$ if and only if every Laurent coefficient of $a$, viewed in $\mathrm{LaurentSeries}\,L$, lies in the image of the maximal ideal of $A$ under $A \to L$.
--
--   (iv) Semilinear action with linear part $d\cdot\mathrm{diag}(1,(d^{q})^{-1})$. For every $d \in (\mathbb{Z}/q)^{\times}$, every ring automorphism $\sigma_L$ of $L$ and every ring automorphism $\sigma_A$ of $A$ such that $\sigma_A$ is compatible with $\sigma_L$ along $A \to L$, such that $\sigma_A a - a$ lies in the maximal ideal of $A$ for all $a \in A$, and such that $\sigma_L\zeta = \zeta^{\,\mathrm{val}(d)}$, and for every ring automorphism $\tau$ of $K$ acting on Laurent series coefficientwise through $\sigma_L$, one has: $\tau$ preserves `chartAlgFin A K j`; and for every proof of this preservation, the induced endomorphism of the chart algebra is trivial modulo the prime $y$, and there exist a ring automorphism $\theta$ of $S$, a ring automorphism $\sigma_W$ of $W$ and a matrix $M \in \mathrm{Mat}_{2\times 2}(W)$ such that: $\theta$ transports the image of the chart algebra in $S$ according to $\tau$, as in (ii); $\sigma_W \circ \sigma = \sigma \circ \sigma_A$ on $A$; $\sigma_W w - w$ lies in the maximal ideal of $W$ for all $w \in W$; $\theta$ is $\sigma_W$-semilinear on constants, $\theta(C(w)) = C(\sigma_W w)$; $M$ is the linear part of $\theta$ in the same sense as in (ii); and for all $i,j$,
--   $$M_{ij} \equiv \Big(\big(d \cdot \mathrm{diag}(1,(d^{q})^{-1})\big)_{ij}\Big) \pmod{\mathfrak{m}_W},$$
--   the right-hand side being the representative in $\{0,\dots,q-1\}$ of the corresponding entry of the scalar multiple of `diagOneElem q (d ^ q)⁻¹` $= \begin{pmatrix} 1 & 0 \\ 0 & (d^{q})^{-1}\end{pmatrix}$ by $d$, cast into $W$; since $d^{q} = d$ in $(\mathbb{Z}/q)^{\times}$, this matrix is $\mathrm{diag}(d,1)$.
--
--   This is the local structure of the integral model of the modular curve for $\Gamma_{H_1}(q^2M')$ at a supersingular point in characteristic $q$: the completed local ring is presented as a Drinfeld-type crossing $W[[X_0,X_1]]/(\varpi v - fu)$ with $f \equiv X_0X_1^q - X_0^qX_1$ to order $q+2$, and the presentation is chosen so that it simultaneously records the $A$-algebra structure, the linear parts $c\cdot\gamma$ of the level automorphisms together with the $\ell$-diamond and $\Gamma(q)$ constraints on $c$, the identification of the branch cut out by $X_0$, and the tame inertia action with linear part $\mathrm{diag}(d,1)$. It is obtained by combining the corresponding statement without the inertia clause with the semilinear inertia computation, and feeds the downstream assembly of the same data in the $q \in \{2,3\}$ auxiliary-level frame.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_exists_ringEquiv_adicCompletion_stalk_drinfeldChart_of_levelAut_riders_inertia_of_mem_ssJSet_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevelOne.exists_ringEquiv_adicCompletion_stalk_drinfeldChart_of_levelAut_riders_inertia_of_mem_ssJSet_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hζξ : ζ = ξ ^ ℓ)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : A →+* W)
      (_ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
      (f u v : MvPowerSeries (Fin 2) W) (_ : IsUnit u) (_ : IsUnit v)
      (_ : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
      (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
        MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u}),

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
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
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal) →
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

      (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
        mkS (MvPowerSeries.C (σ ϖ)) ∈ P →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
            mkS (MvPowerSeries.C (1 : W) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W) * MvPowerSeries.X 1 + h) ∈ P) →
        ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
          toC (germY a) ∈ Ideal.comap (e : CMP →+* S) P ↔
            ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
              (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

      (∀ (d : (ZMod q)ˣ) (σL : L ≃+* L) (σA : A ≃+* A),
        (∀ a : A, algebraMap A L (σA a) = σL (algebraMap A L a)) →

        (∀ a : A, σA a - a ∈ IsLocalRing.maximalIdeal A) →

        σL ζ = ζ ^ ((d : ZMod q).val) →
        ∀ τ : ↥K ≃+* ↥K,

          (∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L)) →

          (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
            τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),

            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal)) ∧

            ∃ (θ : S ≃+* S) (σW : W ≃+* W) (M : Matrix (Fin 2) (Fin 2) W),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                θ (e (toC (germY a))) = e (toC (germY ((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧
              (∀ a : A, σW (σ a) = σ (σA a)) ∧
              (∀ w : W, σW w - w ∈ IsLocalRing.maximalIdeal W) ∧
              (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C (σW w))) ∧
              (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                  mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
              (∀ ii jj : Fin 2, M ii jj -
                  ((((d : ZMod q) * ((ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹ : CuspidalType.GL2 q) :
                      Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj).val : ℕ) : W) ∈ IsLocalRing.maximalIdeal W)) := by sorry
