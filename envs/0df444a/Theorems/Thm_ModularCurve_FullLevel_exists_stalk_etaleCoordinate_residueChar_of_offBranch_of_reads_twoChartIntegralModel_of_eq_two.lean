-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_stalk_etaleCoordinate_residueChar_of_offBranch_of_reads_twoChartIntegralModel_of_eq_two
-- name    : ModularCurve.FullLevel.exists_stalk_etaleCoordinate_residueChar_of_offBranch_of_reads_twoChartIntegralModel_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/1caf1d41-9917-5059-8fb2-40950b085b2d
-- title:
--   Étale coordinate and residue character at a good point (q=2)
-- statement:
--   Throughout, $\overline{\mathbb Q}$ denotes `AlgebraicClosure ℚ`, and for a prime $q$ and a level $M'$ with $q\nmid M'$ one writes $\mathcal F:=$ `fieldBar q M'` for the compositum inside $\mathrm{Laurent}(\overline{\mathbb Q})$ of $\overline{\mathbb Q}$ with the function field of $X_{H}(q^2M')$, where `levelH q M'` is the kernel of the reduction $(\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times$, i.e. the subgroup of units congruent to $1$ modulo $q$; further $\mathcal F_{0}:=$ `modularFunctionFieldBar M'`, the base change to $\overline{\mathbb Q}$ of the full level-$M'$ modular function field. A `Place K F` is a valuation subring of $F$, not all of $F$, containing the image of $K$ and a principal ideal ring; `ord`, `evalAt` and `IsRational` are the associated order function, the evaluation (residue followed by the inverse of $K\to$ residue field) and the surjectivity of $K$ onto the residue field.
--
--   The data are: a prime $q$ with $q=2$ (hypothesis `hq2`); a level $M'\neq 0$ with $q\nmid M'$; a valuation subring $A\subseteq\overline{\mathbb Q}$ with $q\in A^{\mathrm{nonunits}}$ (`hA`); a finite set $W$ of places of `modularFunctionFieldC (ResidueField A) M'` over $k:=\mathrm{ResidueField}\,A$ which, by `hW`, consists exactly of the supersingular places (rational affine geometric places whose value at the generic $j$-invariant lies in `ssJSet q k`); the inclusion $\mathcal F_{0}\le\mathcal F$ (`hle`); a constant reduction datum $R_0$ from $A$ for $\mathcal F_0$ with residues in `modularFunctionFieldC k M'` (a valuation subring $R_0.\mathrm{integers}$ of $\mathcal F_0$, a surjective residue homomorphism onto `modularFunctionFieldC k M'` with kernel the maximal ideal, inducing reduction on constants, together with a degree-preserving place map compatible with divisors of functions and the property that every nonzero function has a constant multiple with nonzero residue), and the hypothesis `hR₀` that for Laurent series $y$ with coefficients in $A$ whose image lies in $\mathcal F_0$ the $R_0$-residue is the coefficientwise reduction of $y$; a primitive $q$-th root of unity $\zeta$ (an element of `Idx q`); and two families of valuation subrings of $\mathcal F$, namely $O_{\mathrm{Ig}}$ indexed by the projective line [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21) over $\mathbb Z/q$ and $O_{\mathrm{SS}}$ indexed by $W$.
--
--   The hypotheses on the Igusa family are: `hIg_inf`, that $O_{\mathrm{Ig}}(\infty)$ is the Gauss ring, $f\in O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$ if and only if $f=x/y$ for Laurent series $x,y$ with coefficients in $A$ and $y$ of nonzero reduction; `hIg`, that every line $\ell$ is of the form $\mathrm{redQ}\,q\,\gamma\cdot\infty$ for some $\gamma\in\Gamma_0(M')$ with $O_{\mathrm{Ig}}(\ell)$ the pullback of $O_{\mathrm{Ig}}(\infty)$ along `levelAutBar q M' ζ γ`; `hIg_inj`, injectivity of $O_{\mathrm{Ig}}$; and `hIg_perm`, that for every root of unity $\zeta'$ and every $\gamma\in\Gamma_0(M')$ the pullbacks along `levelAutBar q M' ζ' γ` permute the family. The hypotheses on the supersingular family are: `hSS_A`, that for each $s\in W$ a constant lies in $O_{\mathrm{SS}}(s)$ exactly when it lies in $A$; `hSS_over`, that for $f\in R_0.\mathrm{integers}$ which is regular at every place of $\mathcal F_0$ at which $j$ is regular and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $\mathcal F$ lies in $O_{\mathrm{SS}}(s)$, and for every $a\in A$ whose residue is the value of the $R_0$-residue of $f$ at $s$ the difference $f-a$ lies in the maximal ideal of $O_{\mathrm{SS}}(s)$; `hSS_fix`, that each $O_{\mathrm{SS}}(s)$ is invariant under all `levelAutBar q M' ζ' γ` with $\gamma\in\Gamma_0(M')$; and `hSS_tr`, that each $O_{\mathrm{SS}}(s)$ contains an element $t$ such that $t-a$ is a unit of $O_{\mathrm{SS}}(s)$ for every $a\in A$.
--
--   Further data: a regular prolongation $R$ of $A$ for $\mathcal F$ with residues in `xHFunctionFieldC k (q^2*M') (levelH q M')` (the same structure as a constant reduction datum, without the place map), subject to `hR`, $R.\mathrm{integers}=O_{\mathrm{Ig}}(\infty)$, and `hR₀O`, that $f\in R_0.\mathrm{integers}$ if and only if the image of $f$ in $\mathcal F$ lies in $O_{\mathrm{Ig}}(\infty)$; an element $\pi\in A$ with $\pi^{q^2-1}=q$; a subfield $k_0\subseteq\overline{\mathbb Q}$ and $\pi_0\in k_0\cap A$ such that $A\cap k_0$ is a henselian discrete valuation ring with maximal ideal generated by $\pi_0$ and with algebraically closed residue field, together with `hκ`, that every element of $A$ is congruent modulo the maximal ideal of $A$ to an element of $k_0\cap A$; an auxiliary prime $\ell\ge 3$ with $\ell\neq q$ and $\ell\nmid M'$, an element $\zeta_0\in k_0$ which is a primitive $q\ell$-th root of unity, and an element $\varpi_t\in k_0\cap A$ with $\varpi_t^{q^2-1}=q\,u$ for some unit $u$ of $A$; finally a finite extension $K_1$ of $k_0$ inside $\overline{\mathbb Q}$ and a valuation subring $A_1$ of $K_1$ with $A_1=A\cap K_1$ (`hA₁`), which is a henselian discrete valuation ring.
--
--   The conclusion is asserted for $\mathcal F$ regarded as a $k_0$-algebra through $\overline{\mathbb Q}$, and for every intermediate field $F_0$ of $\mathcal F/k_0$ satisfying four conditions: the compositum of $F_0$ with $k_0(\overline{\mathbb Q})$ is all of $\mathcal F$; $F_0$ is stable under all `levelAutBar q M' ζ' γ` with $\gamma\in\Gamma_0(M')$; a regularity (linear disjointness) condition, namely that for every finite extension $K'$ of $k_0$ inside $\overline{\mathbb Q}$, every $m$, every $c:\mathrm{Fin}\,m\to\overline{\mathbb Q}$ which is $K'$-linearly independent and every family $a$ of elements of the compositum $k_0(K')\cdot F_0$ with $\sum_i c_i a_i=0$, all $a_i$ vanish; and $F_0$ contains every element of $\mathcal F$ whose Laurent series has rational coefficients (lies in the range of `coeffEmb`). Write $T_1$ for the compositum $k_0(K_1)\cdot F_0$ inside $\mathcal F$, i.e. `IntermediateField.adjoin k₀ (algebraMap '' K₁) ⊔ F₀`. The conclusion is asserted further for every $A_1$-algebra structure on $T_1$ whose structure map sends $a\in A_1$ to the image of $a\in K_1\subseteq\overline{\mathbb Q}$ in $\mathcal F$, and for every $j_1\in T_1$ whose image in $\mathcal F$ is the element of $\mathcal F_0$ given by the Laurent expansion of $j$ (that is, `coeffEmb` applied to `jq`), with $j_1\neq 0$; let $\mathfrak X_1:=$ `TwoChartIntegralModel A₁ T₁ j₁`, the pushout of the two affine charts $X_{\mathrm{Fin}}=\operatorname{Spec}$ `chartAlgFin A₁ T₁ j₁` and $X_{\mathrm{Inf}}=\operatorname{Spec}$ `chartAlgInf A₁ T₁ j₁` (the integral closures in $T_1$ of $A_1[j_1]$, respectively $A_1[j_1^{-1}]$) along their common open, with structure morphism `toBase` to $\operatorname{Spec} A_1$.
--
--   Five predicates on points $x\in\mathfrak X_1$ are introduced. `InStalk x f`, for $f\in T_1$: for every point $y$ of $X_{\mathrm{Fin}}$ mapping to $x$ there are $g,h$ in `chartAlgFin` with $h\notin y$ and $fh=g$, and likewise for $X_{\mathrm{Inf}}$ with `chartAlgInf`; thus $f$ lies in the stalk at $x$ in both charts. `InMax x f`: the same, with the extra requirement $g\in y$ in each chart. `Centred P x`, for a place $P$ of $\mathcal F$ over $\overline{\mathbb Q}$: $P$ is rational and every $f$ with `InStalk x f` lies in the valuation subring of $P$, has $P$-value in $A$, and this value has $A$-valuation $<1$ exactly when `InMax x f` holds; this predicate does not occur in the conclusion. `GoodPt x`: `toBase` sends $x$ to the closed point of $\operatorname{Spec} A_1$; $x$ is closed, in the sense that $x\rightsquigarrow y$ forces $y=x$; for every $y$ over $x$ in either chart, every chart element whose image in $\mathcal F$ is a non-unit of $R.\mathrm{integers}$ lies in the prime $y$; and for every $y$ over $x$ in the finite chart, every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from `chartAlgFin` to $\Omega$ with kernel $y$, the value $\varphi(j_1)$ avoids `ssJSet q Ω`. `Reads x Q`, for a place $Q$ of `xHFunctionFieldC k (q^2*M') (levelH q M')` over $k$: every $f$ with `InStalk x f` lies in $R.\mathrm{integers}$, its $R$-residue lies in the valuation subring of $Q$, and that residue is a non-unit there exactly when `InMax x f` holds. `OffBranch x`: for every line $\ell\neq\infty$ and every $y$ over $x$ in either chart there is a chart element which is a non-unit of $O_{\mathrm{Ig}}(\ell)$ and does not lie in $y$.
--
--   Under these hypotheses: for every point $x$ of $\mathfrak X_1$ and every place $Q$ of `xHFunctionFieldC k (q^2*M') (levelH q M')` over $k$ with `GoodPt x`, `OffBranch x` and `Reads x Q`, there exist a subring $S\subseteq\mathcal F$, a ring homomorphism $\varphi:A_1[X]\to S$ and a ring homomorphism $\chi:S\to\mathrm{ResidueField}\,A$ such that all of the following hold.
--
--   (1) $S$ is the stalk: $f\in S$ if and only if $f\in T_1$ and `InStalk x f`. (2) The kernel of $\chi$ is the maximal ideal of the stalk: for $f\in S$, $\chi(f)=0$ if and only if $f\in T_1$ and `InMax x f`. (3) The map sending $a\in A_1$ to the residue in $\mathrm{ResidueField}\,A$ of the corresponding element of $A$ is surjective. (4) For every $a\in A_1$ the image of $a$ in $\mathcal F$ lies in $S$. (5) $\varphi(C\,a)$ is that image, for every $a\in A_1$. (6) $\chi(\varphi(C\,a))$ is the residue of $a$ in $\mathrm{ResidueField}\,A$, for every $a\in A_1$. (7) $\chi(\varphi(X))=0$. (8) $S$ carries a local ring structure for which $\ker\chi$ is its maximal ideal. (9) $\varphi$ is formally smooth, formally unramified and of essentially finite type. (10) Every $f\in T_1$ is a fraction from $S$: there are $g,h\in S$ with $h\neq 0$ and $fh=g$. (11) Every element of $S$ lies in $R.\mathrm{integers}$, and, for every uniformiser $\varpi$ of $A_1$ (that is, $\mathfrak m_{A_1}=(\varpi)$) and every $f\in S$, $f$ lies in the maximal ideal of $R.\mathrm{integers}$ if and only if $\varphi(C\,\varpi)$ divides $f$ in $S$. (12) For every $f\in S$ the $R$-residue of $f$ lies in the valuation subring of $Q$ and its residue in the residue field of $Q$ is the image of $\chi(f)$ under $\mathrm{ResidueField}\,A\to Q.\mathrm{ResidueField}$. (13) $\varphi(X)$ lies in $R.\mathrm{integers}$ and its $R$-residue has order $1$ at $Q$.
--
--   Unlike the general statement for two-chart integral models that it cites, this conclusion does not assert that the maximal ideal of $S$ is generated by $\varphi(C\,\varpi)$ and $\varphi(X)$, nor surjectivity of $\chi$ as a separate clause.
--
--   This is the per-point step on the Igusa leg of the semistable covering construction for $q=2$: at a closed point of the special fibre of the two-chart integral model which lies off all Igusa branches other than the one at infinity, avoids supersingular $j$-invariants, and reads a place $Q$ of the reduced level field, the stalk is presented as a smooth $A_1[X]$-algebra whose coordinate $X$ reduces to a uniformiser at $Q$ and whose residue character is computed by the regular prolongation $R$. It is used in the assembly of the smooth Igusa base model, [`ModularCurve.FullLevel.exists_igusaBaseModel_smoothPointStalks_of_eq_two`](thm.html#ModularCurve.FullLevel.exists_igusaBaseModel_smoothPointStalks_of_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_stalk_etaleCoordinate_residueChar_of_offBranch_of_reads_twoChartIntegralModel_of_eq_two.lean

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

open CategoryTheory AlgebraicGeometry ModularCurve IsLocalRing CongruenceSubgroup
open AlgebraicCurve
open ModularCurve.FullLevel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.exists_stalk_etaleCoordinate_residueChar_of_offBranch_of_reads_twoChartIntegralModel_of_eq_two
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

    let InStalk : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let InMax : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let Centred : Place (AlgebraicClosure ℚ) ↥(fieldBar q M') → ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun P x =>
      P.IsRational ∧ ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A ∧
          (A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ InMax x f)

    let GoodPt : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      (AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base x = closedPoint ↥A₁ ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), x ⤳ y → y = x) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ = y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω)

    let Reads : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Prop := fun x Q =>
      ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring ∧
          (R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring.nonunits ↔ InMax x f)

    let OffBranch : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      ∀ ℓ : CuspidalType.ProjLine q, ℓ ≠ lineInfty q →
        (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
          ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits ∧ b ∉ y.asIdeal) ∧
        (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
          ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits ∧ b ∉ y.asIdeal)

    ∀ (x : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)) (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))), GoodPt x → OffBranch x → Reads x Q →
      ∃ (S : Subring ↥(fieldBar q M')) (φ : Polynomial ↥A₁ →+* ↥S) (χ : ↥S →+* ResidueField ↥A),

        (∀ f : ↥(fieldBar q M'), f ∈ S ↔ ∃ hf : f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀, InStalk x ⟨f, hf⟩) ∧

        (∀ f : ↥S, χ f = 0 ↔ ∃ hf : (f : ↥(fieldBar q M')) ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀, InMax x ⟨(f : ↥(fieldBar q M')), hf⟩) ∧

        Function.Surjective (fun a : ↥A₁ => IsLocalRing.residue ↥A ⟨((a : ↥K₁) : AlgebraicClosure ℚ), (hA₁ a).mp a.2⟩) ∧

        (∀ a : ↥A₁, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ) ∈ S) ∧
        (∀ a : ↥A₁, ((φ (Polynomial.C a) : ↥S) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) ∧
        (∀ a : ↥A₁, χ (φ (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥K₁) : AlgebraicClosure ℚ), (hA₁ a).mp a.2⟩) ∧
        χ (φ Polynomial.X) = 0 ∧

        (∃ _ : IsLocalRing ↥S, RingHom.ker χ = IsLocalRing.maximalIdeal ↥S) ∧

        φ.FormallySmooth ∧ φ.FormallyUnramified ∧ φ.EssFiniteType ∧

        (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥S, (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

        (∃ hSR : ∀ f : ↥S, (f : ↥(fieldBar q M')) ∈ R.integers,
          ∀ (ϖ : ↥A₁), IsLocalRing.maximalIdeal ↥A₁ = Ideal.span {ϖ} →
            ∀ f : ↥S, (⟨(f : ↥(fieldBar q M')), hSR f⟩ : ↥R.integers) ∈ IsLocalRing.maximalIdeal ↥R.integers ↔ φ (Polynomial.C ϖ) ∣ f) ∧

        (∀ f : ↥S, ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
          IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
            algebraMap (ResidueField ↥A) Q.ResidueField (χ f)) ∧

        (∃ hR : ((φ Polynomial.X : ↥S) : ↥(fieldBar q M')) ∈ R.integers,
          Q.ord (R.residue ⟨((φ Polynomial.X : ↥S) : ↥(fieldBar q M')), hR⟩) = 1) := by sorry
