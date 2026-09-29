-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_constantTerm_chartAlgInf_twoChartIntegralModel_levelField_of_eq_two
-- name    : ModularCurve.FullLevel.exists_constantTerm_chartAlgInf_twoChartIntegralModel_levelField_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/64b3b7b1-34d5-5896-b46c-e71a2927be46
-- title:
--   Constant-term section on the ∞-chart algebra at q=2
-- statement:
--   Throughout, $q$ is a prime with $q=2$ (hypothesis `hq2`), $M'$ is a nonzero natural number with $q \nmid M'$ (`hqM'`), and $A$ is a valuation subring of $\overline{\mathbb Q}$ lying over $q$ in the sense of `LiesOverPrime`, i.e. $q$ belongs to the non-units of $A$ (`hA`). Two function fields occur: $\overline{F}_{M'} :=$ `modularFunctionFieldBar M'`, the field obtained by adjoining to $\overline{\mathbb Q}$ the coefficientwise images under `coeffEmb` of the rational full level-$M'$ modular function field inside $\overline{\mathbb Q}$-Laurent series, and $F :=$ `fieldBar q M'` $=$ `xHFunctionFieldBar (q^2 * M') (levelH q M')`, the analogous base change of the $X_H$-function field of level $q^2M'$ for $H =$ `levelH q M'`, the kernel of the reduction map $(\mathbb Z/q^2M')^{\times} \to (\mathbb Z/q)^{\times}$. The hypothesis `hle` asserts $\overline{F}_{M'} \le F$.
--
--   The characteristic-$p$ side is described by a finite set $W$ of places of `modularFunctionFieldC (ResidueField A) M'` over the residue field of $A$, which by `hW` is exactly the set `ssPlaces q M' (ResidueField A)` of supersingular places (rational places, affine geometric, whose value at the geometric $j$-generator lies in the supersingular $j$-set), together with a constant reduction datum $R_0$ of type `ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M')`: a valuation subring `R₀.integers` of $\overline{F}_{M'}$ lying over $A$, a surjective residue homomorphism onto the level-$M'$ modular function field over `ResidueField A` with kernel the maximal ideal, compatible with reduction of constants, together with the associated map on places. The hypothesis `hR₀` says that $R_0$ computes coefficientwise reduction: for every Laurent series $y$ over $A$ whose image under `coeffMap A.subtype` lies in $\overline{F}_{M'}$, that image lies in `R₀.integers` and its $R_0$-residue, read as a Laurent series over `ResidueField A`, is the coefficientwise reduction `coeffMap (residue ↥A) y` of $y$.
--
--   Further data: a primitive $q$-th root of unity $\zeta$ (an element of `Idx q`), a family $O_{\mathrm{Ig}}$ of valuation subrings of $F$ indexed by the projective line [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21) over $\mathbb Z/q$, and a family $O_{\mathrm{SS}}$ of valuation subrings of $F$ indexed by $W$. The Igusa family is constrained by four hypotheses. `hIg_inf` identifies the member at the point `lineInfty q` $=[1:0]$ as the Gauss ring: $f$ lies in it if and only if there are Laurent series $x,y$ over $A$ with $y$ having nonzero coefficientwise reduction and $f \cdot \mathrm{coeffMap}(A \hookrightarrow \overline{\mathbb Q})(y) = \mathrm{coeffMap}(A \hookrightarrow \overline{\mathbb Q})(x)$ in $\overline{\mathbb Q}$-Laurent series. `hIg` says each index $\ell$ is reached from $[1:0]$ by some $\gamma \in \Gamma_0(M')$: there is $\gamma$ with $\mathrm{red}_q(\gamma)\cdot[1:0] = \ell$ and $O_{\mathrm{Ig}}(\ell)$ equal to the pullback of $O_{\mathrm{Ig}}([1:0])$ along `levelAutBar q M' ζ γ`. `hIg_inj` says $O_{\mathrm{Ig}}$ is injective, and `hIg_perm` says that for every index $\zeta'$ and every $\gamma \in \Gamma_0(M')$ pullback along `levelAutBar q M' ζ' γ` permutes the family, via some permutation $\sigma$ of `ProjLine q` with $(O_{\mathrm{Ig}}(\ell)).\mathrm{comap} = O_{\mathrm{Ig}}(\sigma \ell)$.
--
--   The supersingular family is constrained as follows. `hSS_A` says each $O_{\mathrm{SS}}(s)$ lies over $A$ exactly: for $x \in \overline{\mathbb Q}$, the image of $x$ in $F$ lies in $O_{\mathrm{SS}}(s)$ iff $x \in A$. `hSS_over` is a centring condition: for $s \in W$ and $f \in$ `R₀.integers` such that $f$ has non-negative order at every place $P$ of $\overline{F}_{M'}$ over $\overline{\mathbb Q}$ at which the $j$-expansion `coeffEmb Qbar jq` (viewed in $\overline{F}_{M'}$) has non-negative order, if the $R_0$-residue of $f$ lies in the valuation subring of the place $s$, then the image of $f$ in $F$ under the inclusion given by `hle` lies in $O_{\mathrm{SS}}(s)$, and moreover for every $a \in A$ whose residue equals $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$, the difference of the image of $f$ and the image of $a$ lies in $O_{\mathrm{SS}}(s)$ and in its maximal ideal. `hSS_fix` says each $O_{\mathrm{SS}}(s)$ is invariant under pullback along every `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$, and `hSS_tr` provides for each $s$ an element $t \in O_{\mathrm{SS}}(s)$ such that for every $a \in A$ the difference $t - a$ lies in $O_{\mathrm{SS}}(s)$ and is a unit there.
--
--   Next, $R$ is a regular prolongation of type `RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q^2 * M') (levelH q M'))` — a valuation subring of $F$ over $A$ with surjective residue map onto the level-$q^2M'$ function field over `ResidueField A`, kernel the maximal ideal, compatible with constants, and with the scaling property `exists_smul_mem` — whose ring of integers is the Gauss ring: `hR` asserts `R.integers = OIg (lineInfty q)`. The hypothesis `hR₀O` says that `R₀.integers` is the preimage of that Gauss ring: $f \in$ `R₀.integers` iff the image of $f$ in $F$ lies in $O_{\mathrm{Ig}}([1:0])$.
--
--   Arithmetic data over the base complete the list. There is $\pi \in \overline{\mathbb Q}$ with $\pi^{q^2-1} = q$ and $\pi \in A$. There is a subfield $k_0 \subseteq \overline{\mathbb Q}$ and $\pi_0 \in k_0$ with $\pi_0 \in A$ such that $A \cap k_0$ (the pullback of $A$ along $k_0 \hookrightarrow \overline{\mathbb Q}$) is a discrete valuation ring (`hdvr`) with maximal ideal generated by $\pi_0$ (`hunif`), is henselian local (`hhens`) and has algebraically closed residue field (`hres`); `hκ` says every $a \in A$ is congruent modulo the maximal ideal of $A$ to an element of $k_0$ lying in $A$. There is an auxiliary prime $\ell \ge 3$ with $\ell \ne q$ and $\ell \nmid M'$, an element $\zeta_0 \in k_0$ which is a primitive $q\ell$-th root of unity in $\overline{\mathbb Q}$, and an element $\varpi_t \in k_0$ lying in $A$ with $\varpi_t^{q^2-1} = q \cdot u$ for some unit $u$ of $A$. Finally $K_1$ is a finite extension of $k_0$ inside $\overline{\mathbb Q}$ and $A_1$ is a valuation subring of $K_1$ with $x \in A_1 \iff x \in A$ (`hA₁`), assumed to be a henselian discrete valuation ring.
--
--   The field $F$ is given the $k_0$-algebra structure obtained by composing $k_0 \hookrightarrow \overline{\mathbb Q}$ with $\overline{\mathbb Q} \to F$. The assertion is then made for every intermediate field $F_0$ of $F/k_0$ satisfying four conditions: the compositum of $F_0$ with the $k_0$-subfield generated by the constants $\overline{\mathbb Q}$ is all of $F$; $F_0$ is stable under every `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$; a linear disjointness condition, namely for every intermediate field $K'$ finite over $k_0$, every $m$, every $c : \mathrm{Fin}\,m \to \overline{\mathbb Q}$ linearly independent over $K'$ and every family $a_i$ of elements of $\mathrm{adjoin}_{k_0}(\text{image of } K') \sqcup F_0$, the relation $\sum_i c_i a_i = 0$ forces all $a_i = 0$; and $F_0$ contains every element of $F$ whose Laurent series lies in the range of `coeffEmb (AlgebraicClosure ℚ)`.
--
--   Write $T_1 := \mathrm{adjoin}_{k_0}(\text{image of } K_1 \text{ in } F) \sqcup F_0$. The statement quantifies over every $A_1$-algebra structure on $T_1$ whose structure map is compatible with the inclusions, i.e. for $a \in A_1$ the image of $a$ in $T_1$, viewed in $F$, is the image of $a \in K_1 \subseteq \overline{\mathbb Q}$ under $\overline{\mathbb Q} \to F$; and over every $j_1 \in T_1$ with $j_1 \ne 0$ whose image in $F$ is the inclusion (via `hle`) of the element of $\overline{F}_{M'}$ given by the $q$-expansion `coeffEmb Qbar jq` of the modular invariant.
--
--   Under these hypotheses there exists a ring homomorphism
--   $$\psi : \mathrm{chartAlgInf}(A_1, T_1, j_1) \longrightarrow A_1,$$
--   where `chartAlgInf A₁ T₁ j₁` is the subalgebra of elements of $T_1$ integral over $A_1[j_1^{-1}]$, such that all of the following hold: $\psi$ is a section of the structure map, i.e. $\psi(\mathrm{algebraMap}\,a) = a$ for all $a \in A_1$; $\psi$ annihilates `jInvChartInf A₁ T₁ j₁`, the element $j_1^{-1}$ of the chart algebra; for every $b$ in the chart algebra, the image of $b$ in $F$ lies in `qIntegersBar (AlgebraicClosure ℚ) (fieldBar q M')`, the valuation subring of elements whose Laurent series has non-negative order; for every $b$ in the chart algebra, the coefficient at $0$ of the Laurent series over $\overline{\mathbb Q}$ attached to the image of $b$ in $F$ equals the image of $\psi(b)$ under $A_1 \subseteq K_1 \subseteq \overline{\mathbb Q}$; and for every $b$ in the chart algebra whose image in $F$ lies in the non-units of `R.integers`, the value $\psi(b)$ lies in the maximal ideal of $A_1$.
--
--   This is the $q = 2$ case of the construction of the constant-term homomorphism on the $\infty$-chart (pole chart) of the two-chart integral model of the level field over the henselian discrete valuation ring $A_1$: it exhibits the chart algebra as consisting of $q$-expansions holomorphic at the cusp, with the constant term as an $A_1$-valued section that kills $j^{-1}$ and carries non-units of the Gauss ring into the maximal ideal. It is used by [`ModularCurve.FullLevel.exists_centred_of_toValuationSubring_eq_qIntegersBar_twoChartIntegralModel_of_eq_two`](thm.html#ModularCurve.FullLevel.exists_centred_of_toValuationSubring_eq_qIntegersBar_twoChartIntegralModel_of_eq_two), where places of the level field are centred at points of the special fibre of the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_constantTerm_chartAlgInf_twoChartIntegralModel_levelField_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.exists_constantTerm_chartAlgInf_twoChartIntegralModel_levelField_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))

    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ₀ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ₀⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    [IsDiscreteValuationRing ↥A₁] [HenselianLocalRing ↥A₁] :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →

    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],
    ∃ ψ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* ↥A₁,
      (∀ a : ↥A₁, ψ (algebraMap ↥A₁ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) a) = a) ∧
      ψ (AlgebraicCurve.TwoChartIntegralModel.jInvChartInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) = 0 ∧
      (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁),
        ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ qIntegersBar (AlgebraicClosure ℚ) (fieldBar q M')) ∧
      (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁),
        ((((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))).coeff 0 =
          (((ψ b : ↥A₁) : ↥K₁) : AlgebraicClosure ℚ)) ∧
      (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁),
        ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → ψ b ∈ maximalIdeal ↥A₁) := by sorry
