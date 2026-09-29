-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_SemistableCovering_exists_semistableModel_descent_of_discCharts_of_noCuspFreePackageSS_of_jPins_of_nodeRings_nodeCharts
-- name    : ModularCurve.FullLevel.SemistableCovering.exists_semistableModel_descent_of_discCharts_of_noCuspFreePackageSS_of_jPins_of_nodeRings_nodeCharts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/7f81bbc0-e653-5c95-bb31-3cd49473e41d
-- title:
--   Semistable model with descent from a disc-charted covering
-- statement:
--   Fix a prime $q\ge 5$ and a natural number $M'$ with $M'\neq 0$ and $q\nmid M'$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$, in the sense that $q$ is a non-unit of $A$ (`A.LiesOverPrime q`), write $k=\mathrm{ResidueField}\,A$, and let $W$ be a finite set of places of the field $\mathtt{modularFunctionFieldC}\,k\,M'=k(j,j_{M'})$ over $k$; the hypothesis `hW` says that $W$ consists exactly of the supersingular places in the sense of `ssPlaces q M' k`. Let `hle` be an inclusion $\overline{\mathbb Q}\cdot F(\Gamma(M')) \le \mathtt{fieldBar}\,q\,M'$ of the base-changed modular function field into the full-level field $F=\mathtt{fieldBar}\,q\,M'$ (the base change to $\overline{\mathbb Q}$ of the function field of the $H$-level curve of level $q^2M'$), and let $R_0$ be a `ConstantReduction` of $A$ from that modular function field to $k(j,j_{M'})$, i.e. a valuation subring of the source whose intersection with the constants is $A$, together with a surjective residue homomorphism onto $k(j,j_{M'})$ with kernel the maximal ideal, compatible with the residue map of $A$, satisfying the scaling and degree/divisor clauses of that structure. The hypothesis `hR₀` requires that a Laurent series over $A$ whose coefficientwise image lies in the base-changed modular function field lies in $R_0$'s ring of integers, with $R_0$-residue equal to the coefficientwise reduction of the series modulo the maximal ideal of $A$.
--
--   Further data: an element $\pi\in\overline{\mathbb Q}$ with $\pi^{q^2-1}=q$ and $\pi\in A$; a ring homomorphism $\iota$ from the field $\mathbb F_{q^2}$ to $k$; the Drinfeld coordinate ring $\mathtt{CoordRing}\,q\,k$ is assumed to be a domain; an index $\zeta$ of a primitive $q$-th root of unity in $\overline{\mathbb Q}$; and two families of valuation subrings of $F$, namely $O^{\mathrm{Ig}}_\ell$ indexed by $\ell\in\mathbb P^1(\mathbb F_q)$ and $O^{\mathrm{ss}}_s$ indexed by $s\in W$.
--
--   The Igusa family is constrained by four hypotheses: `hIg_inf` describes $O^{\mathrm{Ig}}_{\infty}$ (at the line `lineInfty q`) as the set of $f\in F$ whose Laurent expansion can be written as a quotient $x/y$ of coefficientwise images of Laurent series over $A$ with $y$ of non-zero reduction; `hIg` requires every $\ell$ to be reached from $\infty$ by some $\gamma\in\Gamma_0(M')$ with $\mathrm{red}_q(\gamma)\cdot\infty=\ell$ and $O^{\mathrm{Ig}}_\ell$ the pullback of $O^{\mathrm{Ig}}_\infty$ along the level automorphism $\mathtt{levelAutBar}\,q\,M'\,\zeta\,\gamma$; `hIg_inj` requires $\ell\mapsto O^{\mathrm{Ig}}_\ell$ to be injective; `hIg_perm` requires, for every root-of-unity index $\zeta'$ and every $\gamma\in\Gamma_0(M')$, that pullback along $\mathtt{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ permute the family.
--
--   The supersingular family is constrained by three hypotheses. `hSS_A` says that a constant of $\overline{\mathbb Q}$ lies in $O^{\mathrm{ss}}_s$ exactly when it lies in $A$. `hSS_over` says that for $f$ in $R_0$'s integers which is regular at every place at which $\bar j$ (the image in the base-changed modular function field of the Laurent $j$-series $\mathtt{jq}$) is regular, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $F$ lies in $O^{\mathrm{ss}}_s$, and for every $a\in A$ whose residue equals the value of the $R_0$-residue of $f$ at $s$ the difference $f-a$ lies in the maximal ideal of $O^{\mathrm{ss}}_s$. `hSS_fix` says each $O^{\mathrm{ss}}_s$ is invariant under pullback by every $\mathtt{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma\in\Gamma_0(M')$, and `hSS_tr` provides for each $s$ an element $t\in O^{\mathrm{ss}}_s$ such that $t-a$ is a unit of $O^{\mathrm{ss}}_s$ for every $a\in A$.
--
--   Let $\mathcal C$ be a `SemistableCovering q M' A W`: Igusa component fields $F^{\mathrm{Ig}}_\ell$ and supersingular component fields $F^{\mathrm{ss}}_s$ over $k$, component charts $C^{\mathrm{Ig}}_\ell$, $C^{\mathrm{ss}}_s$ of $F$ with values in them, paired annuli $\mathrm{An}(\ell,s)$, $\mathrm{An}'(\ell,s)$ with equal domains and moduli and multiplicative parameters, attachment data $x_s(\ell,s)$, $x_t(\ell,s)$ at the nodes, the unique-attachment clauses, and the partition clause for places of $F$. The hypothesis `h9` is the conjunction of ten clauses: the chart rings of $\mathcal C$ are the given rings ($(C^{\mathrm{Ig}}_\ell)$'s integers is $O^{\mathrm{Ig}}_\ell$ and $(C^{\mathrm{ss}}_s)$'s integers is $O^{\mathrm{ss}}_s$), together with $\mathcal C.\mathtt{EquivClauses}$ (equivariance of charts, domains and annuli under the level automorphisms up to a permutation of $\mathbb P^1(\mathbb F_q)$), $\mathcal C.\mathtt{LevelPinClauses}\ \mathtt{hle}\ R_0$ (the $R_0$-residues read correctly on the supersingular charts via evaluation at $s$, and on each Igusa chart through a homomorphism $j$ of $k(j,j_{M'})$ into $F^{\mathrm{Ig}}_\ell$ detecting the valuation subring of $s$ at $x_s(\ell,s)$), $\mathcal C.\mathtt{InertiaClause}\ \pi$, $\mathcal C.\mathtt{WidthClause}\ \langle\pi,h\pi P\rangle$ (each annulus modulus is a unit times a positive power of $\pi$), $\mathcal C.\mathtt{GenusClause}$, $\mathcal C.\mathtt{DiscFibreClause}$, $\mathcal C.\mathtt{CurveClause}$ and $\mathcal C.\mathtt{NaturalityClauses}$.
--
--   The remaining hypotheses are the charting and local-structure inputs.
--
--   `hIgCharts` and `hSSCharts` require every chart of $\mathcal C$ to be disc-charted: for each $\ell$ (respectively each $s$) there are a regular prolongation $R$ of $A$ in $F$ with values in the component field, a family of sets of places $\mathrm{disc}(Q)$ and coordinates $\mathrm{coord}(Q)$ indexed by the places $Q$ of the component field, such that $R$ has the same ring of integers as the chart and the same residue map on it, $(\mathrm{disc},\mathrm{coord})$ is a `DiscFamily` of $R$ for the chart's node set (each non-node $Q$ has $\mathrm{disc}(Q)$ a residue disc with coordinate $\mathrm{coord}(Q)$, and distinct non-nodes have disjoint discs), the chart's domain is the union of the discs over non-nodes, and the chart's place map is constantly $Q$ on $\mathrm{disc}(Q)$.
--
--   `hNoPkgSS` is an exclusion: for every $s$, every regular prolongation $R$ agreeing with the chart $C^{\mathrm{ss}}_s$ in integers and residue, every node $Q$ of that chart, and every choice of a subring $S\subseteq F$, ring homomorphisms $\varphi_T:A[X]\to S$ and $\chi_0:S\to k$, and set $D$ of places of $F$, the conjunction of thirteen conditions fails. Those conditions (summarised here) require: $S$ to contain the constants of $A$; $\varphi_T$ to be formally smooth and formally unramified and to restrict to the constants correctly, both before and after $\chi_0$; $\chi_0(\varphi_T X)=0$; for each $c$ in the maximal ideal of $A$ a unique $A$-point of $S$ over the identity on constants lifting $\chi_0$ and sending $\varphi_T X$ to $c$; every element of $S$ to be $R$-integral with $R$-residue in $Q$'s valuation subring, reducing there to $\chi_0$; the $R$-residue of $\varphi_T X$ to have order $1$ at $Q$; $D$ to be exactly the rational places at which all of $S$ is integral with values in $A$, the points of value of absolute value $<1$ being those where $\chi_0$ vanishes; each $A$-point of $S$ to come from a unique place of $D$; the valuation subring of each place of $D$ to be the set of fractions of elements of $S$; a unit principle (a non-zero function with order $0$ throughout $D$ is a constant multiple of a unit of $S$); every $R$-integral function integral throughout $D$ to lie in $S$; and finally $\bar j$ to be regular at every place of $D$.
--
--   `hJ'` provides, for each $s$, an element $a\in A$ such that $\bar j-a$ lies in $R_0$'s integers, is regular wherever $\bar j$ is, has $R_0$-residue in the valuation subring of $s$, and that residue evaluates to $0$ at $s$. `hIgJ` says that such a pinned coordinate detects nodes on the Igusa side: for all $\ell$, $s$ and $a$ as above with $R_0$-residue in $s$'s valuation subring and vanishing value at $s$, every place $Q$ of $F^{\mathrm{Ig}}_\ell$ at which the chart residue of the image of $\bar j-a$ is defined and reduces to $0$ belongs to the node set of $C^{\mathrm{Ig}}_\ell$.
--
--   `hAnRing` provides, for each $s$, a regular prolongation $R$ agreeing with $C^{\mathrm{ss}}_s$ in integers and residue, together with a layered node-ring package. The package consists of an index type $\Lambda$ with a distinguished $l_0$, discrete valuation subrings $C'(l)\subseteq A$ of $\overline{\mathbb Q}$ with uniformisers $\varpi'(l)$, complete discrete valuation rings $W_c(l)$ with irreducible elements $\pi(l)$, exponents $E(l)\ge 1$ and $E_0$, subrings $\mathcal N(\ell)$ and local Noetherian subrings $\mathcal N_0(\ell,l)$ of $F$, and coordinates $x,y,u:\mathbb P^1(\mathbb F_q)\to F$, subject to: $\varpi'(l)$ generating the residue-zero elements of $C'(l)$, $C'(l_0)\le C'(l)$, $\varpi'(l_0)\neq 0$, $A$ algebraic over $C'(l_0)$, and, for each $\ell$: the annulus parameter of $\mathrm{An}(\ell,s)$ is $y(\ell)$ and its modulus is $\varpi'(l_0)^{E_0}$; $x_s(\ell,s)$, $x_t(\ell,s)$ and all places of the annulus domain are rational; $\mathcal N(\ell)$ is the intersection of the Igusa chart ring, $R$'s integers and the valuation subrings of the annulus domain, and its elements take values in $A$ there; the crossing relation $x(\ell)\,y(\ell)=\varpi'(l_0)^{E_0}u(\ell)$ holds; $x(\ell)$ has Igusa residue $0$ and $R$-residue of order $1$ at $x_t(\ell,s)$, while $y(\ell)$ has $R$-residue $0$ and Igusa residue of order $1$ at $x_s(\ell,s)$; $F$ is the fraction field of the $\mathcal N_0(\ell,l)$ and is spanned over $\mathcal N_0(\ell,l_0)$ by finitely many constants; and for each $l$: the nesting $\mathcal N_0(\ell,l_0)\le\mathcal N_0(\ell,l)\le\mathcal N(\ell)$, a characterisation of the annulus domain as the places where $\mathcal N_0(\ell,l)$ is integral and non-units are sent into the maximal ideal of $A$, the constants of $C'(l)$ lying in $\mathcal N_0(\ell,l)$ and exhausting its residues, a $C'(l)$-linear independence clause, existence of a subring $B_x$ generated over the constants of $C'(l)$ by a finite set, containing $x(\ell),y(\ell),u(\ell)$, of which $\mathcal N_0(\ell,l)$ is the localisation, membership of $x(\ell),y(\ell)$ and invertibility of $u(\ell)$ in $\mathcal N_0(\ell,l)$, and finally a homomorphism $\sigma$ from $W_c(l)$ to the adic completion of $\mathcal N_0(\ell,l)$ and an isomorphism $\iota$ of that completion with the crossing model $\mathtt{UVCrossingModel}\,(W_c(l))\,(\pi(l)^{E(l)})$, matching $\sigma(\pi(l))$ with $\varpi'(l)$, $\iota\circ\sigma$ with the constants, all constants of $C'(l)$ with values of $\sigma$, and reading off orders: a function whose Igusa residue is non-zero of order $n$ at $x_s(\ell,s)$ agrees with a unit times $V^n$ modulo the ideal generated by $\pi(l)$ and $U$, and a function whose $R$-residue is non-zero of order $n$ at $x_t(\ell,s)$ agrees with a unit times $U^n$ modulo the ideal generated by $\pi(l)$ and $V$.
--
--   The conclusion asserts the existence of a semistable model $M$ of type $\mathtt{AlgebraicCurve.SemistableModel}\,A\,F$ for the vertex family $\mathcal C.\mathtt{sumFbar}$ (the Igusa and supersingular component fields indexed by $\mathbb P^1(\mathbb F_q)\sqcup W$) with charts $\mathcal C.\mathtt{sumChart}$, with edge family indexed by pairs $e=(\ell,s)\in\mathbb P^1(\mathbb F_q)\times W$ given by the annuli $\mathrm{An}(\ell,s)$, source $\mathrm{inl}\,\ell$ and target $\mathrm{inr}\,s$, and with edge endpoints the node places $\mathcal C.\mathtt{sumNode}(\mathrm{inl}\,\ell)\,e$ and $\mathcal C.\mathtt{sumNode}(\mathrm{inr}\,s)\,e$ — that is, an integral scheme proper, flat and locally of finite presentation over $\operatorname{Spec} A$, with an identification of $F$ with its function field compatible with the structure morphism, and with points realising the places of $F$, the generic points of the components, the non-node places of each component and the nodes, subject to the specialisation and local-ring clauses of that structure — such that moreover $M.\mathtt{Descent}$ is non-empty: the model descends to a Noetherian henselian local ring $A_0$ with an injective local homomorphism into $A$ whose image is the intersection of $A$ with a subfield $K_0$ of $\overline{\mathbb Q}$ over which $\overline{\mathbb Q}$ is algebraic and whose residue map onto $k$ is surjective, via a proper flat finitely presented integral $A_0$-scheme $X_0$ with $M.X$ isomorphic to its base change, the isomorphism compatible with the structure morphisms, generic points and function fields in the sense recorded in that structure.
--
--   This is the global assembly step in the construction of the semistable model over $A$ of the full-level modular curve of level $q^2M'$: from a semistable covering all of whose charts are residue-disc charts, whose supersingular nodes admit no smooth-point package of the excluded shape, and whose nodes carry explicit $UV$-crossing presentations, it produces the semistable $A$-model realising the covering's component–annulus combinatorics together with a descent datum to a henselian local base. It is used by the existence theorem for semistable coverings with equivariance clauses, which in turn feeds the analysis of the reduction of the curve at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_SemistableCovering_exists_semistableModel_descent_of_discCharts_of_noCuspFreePackageSS_of_jPins_of_nodeRings_nodeCharts.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open AlgebraicCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.SemistableCovering.exists_semistableModel_descent_of_discCharts_of_noCuspFreePackageSS_of_jPins_of_nodeRings_nodeCharts
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField A)
    [IsDomain (DrinfeldCurve.CoordRing q (IsLocalRing.ResidueField A))]
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
    (𝒞 : SemistableCovering q M' A W)
    (h9 : (∀ ℓ, (𝒞.CIg ℓ).integers = OIg ℓ) ∧ (∀ s, (𝒞.CSS s).integers = OSS s) ∧
      𝒞.EquivClauses ∧ 𝒞.LevelPinClauses hle R₀ ∧ 𝒞.InertiaClause π ∧
        𝒞.WidthClause ⟨π, hπP⟩ ∧ 𝒞.GenusClause ∧ 𝒞.DiscFibreClause ∧ 𝒞.CurveClause ∧ 𝒞.NaturalityClauses)

    (hIgCharts : ∀ ℓ : CuspidalType.ProjLine q,
      ∃ (R : RegularProlongation A (fieldBar q M') (𝒞.FIg ℓ))
        (disc : Place (ResidueField A) (𝒞.FIg ℓ) → Set (Place (AlgebraicClosure ℚ) (fieldBar q M')))
        (coord : Place (ResidueField A) (𝒞.FIg ℓ) → (fieldBar q M')),
        R.integers = (𝒞.CIg ℓ).integers ∧
        (∀ (f : fieldBar q M') (hC : f ∈ (𝒞.CIg ℓ).integers) (hR : f ∈ R.integers), (𝒞.CIg ℓ).residue ⟨f, hC⟩ = R.residue ⟨f, hR⟩) ∧
        R.DiscFamily (𝒞.CIg ℓ).nodes disc coord ∧
        (∀ P, P ∈ (𝒞.CIg ℓ).dom ↔ ∃ Q, Q ∉ (𝒞.CIg ℓ).nodes ∧ P ∈ disc Q) ∧
        (∀ P Q, Q ∉ (𝒞.CIg ℓ).nodes → P ∈ disc Q → (𝒞.CIg ℓ).placeMap P = Q))
    (hSSCharts : ∀ s : ↥W,
      ∃ (R : RegularProlongation A (fieldBar q M') (𝒞.FSS s))
        (disc : Place (ResidueField A) (𝒞.FSS s) → Set (Place (AlgebraicClosure ℚ) (fieldBar q M')))
        (coord : Place (ResidueField A) (𝒞.FSS s) → (fieldBar q M')),
        R.integers = (𝒞.CSS s).integers ∧
        (∀ (f : fieldBar q M') (hC : f ∈ (𝒞.CSS s).integers) (hR : f ∈ R.integers), (𝒞.CSS s).residue ⟨f, hC⟩ = R.residue ⟨f, hR⟩) ∧
        R.DiscFamily (𝒞.CSS s).nodes disc coord ∧
        (∀ P, P ∈ (𝒞.CSS s).dom ↔ ∃ Q, Q ∉ (𝒞.CSS s).nodes ∧ P ∈ disc Q) ∧
        (∀ P Q, Q ∉ (𝒞.CSS s).nodes → P ∈ disc Q → (𝒞.CSS s).placeMap P = Q))

    (hNoPkgSS : ∀ (s : ↥W) (R : RegularProlongation A ↥(fieldBar q M') (𝒞.FSS s)),
      R.integers = (𝒞.CSS s).integers →
      (∀ (f : ↥(fieldBar q M')) (hC : f ∈ (𝒞.CSS s).integers) (hR : f ∈ R.integers), (𝒞.CSS s).residue ⟨f, hC⟩ = R.residue ⟨f, hR⟩) →
      ∀ (Q : Place (ResidueField ↥A) (𝒞.FSS s)), Q ∈ (𝒞.CSS s).nodes →
      ∀ (S : Subring ↥(fieldBar q M')) (φT : Polynomial ↥A →+* ↥S) (χ₀ : ↥S →+* ResidueField ↥A)
        (D : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
        ¬ (
            (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ S) ∧
            (φT).FormallySmooth ∧ (φT).FormallyUnramified ∧
            (∀ a : ↥A, ((φT (Polynomial.C a) : ↥(S)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ))) ∧
            (∀ a : ↥A, χ₀ (φT (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
            χ₀ (φT Polynomial.X) = 0 ∧
            (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
              ∃! χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φT (Polynomial.C a)) = a) ∧
                (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φT Polynomial.X) = c) ∧
            (∀ f : ↥(S), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
              IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                algebraMap (ResidueField ↥A) Q.ResidueField (χ₀ f)) ∧
            (∃ hR : ((φT Polynomial.X : ↥(S)) : ↥(fieldBar q M')) ∈ R.integers,
              Q.ord (R.residue ⟨((φT Polynomial.X : ↥(S)) : ↥(fieldBar q M')), hR⟩) = 1) ∧
            (∀ P, P ∈ D ↔ (P.IsRational ∧ (∀ f : ↥(S), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
              (∀ f : ↥(S), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χ₀ f = 0))) ∧
            (∀ χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φT (Polynomial.C a)) = a) →
              (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) →
              ∃! P, P ∈ D ∧ ∀ f : ↥(S), P.evalAt (f : ↥(fieldBar q M')) = ((χ f : ↥A) : (AlgebraicClosure ℚ))) ∧
            (∀ P ∈ D, ∀ f : ↥(fieldBar q M'), f ∈ P.toValuationSubring ↔
              ∃ g h : ↥(S), P.evalAt (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
              ∃ (c : (AlgebraicClosure ℚ)) (u : (↥(S))ˣ), c ≠ 0 ∧ algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * f = ((u : ↥(S)) : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S) ∧

            (∀ P ∈ D, 0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')))))

    (hJ' : ∀ s : ↥W, ∃ (a : ↥A) (hj : ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (a : AlgebraicClosure ℚ) ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord (((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (a : AlgebraicClosure ℚ))) ∧
      (R₀.residue ⟨_, hj⟩ : modularFunctionFieldC (ResidueField A) M') ∈
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ∧
      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
        (R₀.residue ⟨_, hj⟩ : modularFunctionFieldC (ResidueField A) M') = 0)

    (hIgJ : ∀ (ℓ : CuspidalType.ProjLine q) (s : ↥W) (a : ↥A) (hj : ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (a : AlgebraicClosure ℚ) ∈ R₀.integers),
      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
        (R₀.residue ⟨_, hj⟩ : modularFunctionFieldC (ResidueField A) M') = 0 →
      (R₀.residue ⟨_, hj⟩ : modularFunctionFieldC (ResidueField A) M') ∈
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
      ∀ (Q : Place (ResidueField ↥A) (𝒞.FIg ℓ))
        (hC : (IntermediateField.inclusion hle (((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (a : AlgebraicClosure ℚ)) : ↥(fieldBar q M')) ∈ (𝒞.CIg ℓ).integers)
        (hm : (𝒞.CIg ℓ).residue ⟨_, hC⟩ ∈ Q.toValuationSubring),
        IsLocalRing.residue ↥Q.toValuationSubring ⟨(𝒞.CIg ℓ).residue ⟨_, hC⟩, hm⟩ = 0 → Q ∈ (𝒞.CIg ℓ).nodes)

    (hAnRing : ∀ s : ↥W, ∃ (R : RegularProlongation A (fieldBar q M') (𝒞.FSS s)),
        R.integers = (𝒞.CSS s).integers ∧
        (∀ (f : fieldBar q M') (hC : f ∈ (𝒞.CSS s).integers) (hR : f ∈ R.integers), (𝒞.CSS s).residue ⟨f, hC⟩ = R.residue ⟨f, hR⟩) ∧

          (∃ (Λ : Type) (C' : Λ → Subring (AlgebraicClosure ℚ)) (hC'A : ∀ (l : Λ) (c : AlgebraicClosure ℚ), c ∈ C' l → c ∈ A)
            (_ : ∀ l, IsDomain ↥(C' l)) (_ : ∀ l, IsDiscreteValuationRing ↥(C' l))
            (ϖ' : ∀ l, ↥(C' l)) (l₀ : Λ)
            (Wc : Λ → Type) (_ : ∀ l, CommRing (Wc l)) (_ : ∀ l, IsDomain (Wc l)) (_ : ∀ l, IsDiscreteValuationRing (Wc l))
            (_ : ∀ l, IsAdicComplete (maximalIdeal (Wc l)) (Wc l))
            (π : ∀ l, Wc l) (E : Λ → ℕ) (E₀ : ℕ)
            (𝒩 : CuspidalType.ProjLine q → Subring (fieldBar q M'))
            (𝒩₀ : CuspidalType.ProjLine q → Λ → Subring (fieldBar q M'))
            (hloc : ∀ ℓ l, IsLocalRing ↥(𝒩₀ ℓ l)) (hnoe : ∀ ℓ l, IsNoetherianRing ↥(𝒩₀ ℓ l))
            (x y u : CuspidalType.ProjLine q → fieldBar q M'),
            (∀ (l : Λ) (d : ↥(C' l)), IsLocalRing.residue A ⟨(d : AlgebraicClosure ℚ), hC'A l d d.2⟩ = 0 ↔ ∃ d' : ↥(C' l), d = ϖ' l * d') ∧
            (∀ l, C' l₀ ≤ C' l) ∧
            ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) ≠ 0 ∧
            (∀ a : AlgebraicClosure ℚ, a ∈ A → IsAlgebraic ↥(C' l₀) a) ∧
            (∀ l, Irreducible (π l)) ∧ (∀ l, 1 ≤ E l) ∧
            (∀ ℓ,

              (𝒞.An ℓ s).param = y ℓ ∧
              ((𝒞.An ℓ s).modulus : AlgebraicClosure ℚ) = ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) ^ E₀ ∧

              (𝒞.xs ℓ s).IsRational ∧ (𝒞.xt ℓ s).IsRational ∧ (∀ P ∈ (𝒞.An ℓ s).dom, P.IsRational) ∧

              (∀ f : fieldBar q M', f ∈ 𝒩 ℓ ↔ f ∈ (𝒞.CIg ℓ).integers ∧ f ∈ R.integers ∧ ∀ P ∈ (𝒞.An ℓ s).dom, f ∈ P.toValuationSubring) ∧
              (∀ f ∈ 𝒩 ℓ, ∀ P ∈ (𝒞.An ℓ s).dom, P.evalAt f ∈ A) ∧

              x ℓ * y ℓ = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) ^ E₀ * u ℓ ∧
              (∀ h₁ : x ℓ ∈ (𝒞.CIg ℓ).integers, (𝒞.CIg ℓ).residue ⟨x ℓ, h₁⟩ = 0) ∧
              (∀ h₂ : x ℓ ∈ R.integers, (𝒞.xt ℓ s).ord (R.residue ⟨x ℓ, h₂⟩) = 1) ∧
              (∀ h₂ : y ℓ ∈ R.integers, R.residue ⟨y ℓ, h₂⟩ = 0) ∧
              (∀ h₁ : y ℓ ∈ (𝒞.CIg ℓ).integers, (𝒞.xs ℓ s).ord ((𝒞.CIg ℓ).residue ⟨y ℓ, h₁⟩) = 1) ∧

              (∀ f : fieldBar q M', ∃ (l : Λ) (a b : ↥(𝒩₀ ℓ l)), (b : fieldBar q M') ≠ 0 ∧ f * (b : fieldBar q M') = (a : fieldBar q M')) ∧
              (∀ f : fieldBar q M', ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀ ℓ l₀)) (b : ↥(𝒩₀ ℓ l₀)),
                (b : fieldBar q M') ≠ 0 ∧ f * (b : fieldBar q M') = ∑ i, c i • ((a i : ↥(𝒩₀ ℓ l₀)) : fieldBar q M')) ∧

              (∀ l, letI : IsLocalRing ↥(𝒩₀ ℓ l) := hloc ℓ l;
                𝒩₀ ℓ l₀ ≤ 𝒩₀ ℓ l ∧ 𝒩₀ ℓ l ≤ 𝒩 ℓ ∧
                (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ (𝒞.An ℓ s).dom ↔
                  (∀ f : fieldBar q M', f ∈ 𝒩₀ ℓ l → f ∈ P.toValuationSubring) ∧
                  (∀ f : ↥(𝒩₀ ℓ l), ¬ IsUnit f → ∃ h : P.evalAt (f : fieldBar q M') ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)) ∧
                (∀ c : AlgebraicClosure ℚ, c ∈ C' l → algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c ∈ 𝒩₀ ℓ l) ∧
                (∀ g : ↥(𝒩₀ ℓ l), ∃ (o : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (o : AlgebraicClosure ℚ) ∈ 𝒩₀ ℓ l), ¬ IsUnit (g - ⟨_, h⟩)) ∧
                (∀ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀ ℓ l)), LinearIndependent ↥(C' l) c →
                  ∑ i, c i • ((a i : ↥(𝒩₀ ℓ l)) : fieldBar q M') = 0 → ∀ i, a i = 0) ∧

                (∃ Bx : Subring (fieldBar q M'),
                  (∀ f : fieldBar q M', f ∈ Bx → f ∈ 𝒩₀ ℓ l) ∧
                  x ℓ ∈ Bx ∧ y ℓ ∈ Bx ∧ u ℓ ∈ Bx ∧
                  (∀ f : fieldBar q M', f ∈ 𝒩₀ ℓ l ↔ ∃ g h : fieldBar q M', g ∈ Bx ∧ h ∈ Bx ∧
                    (∀ hh : h ∈ 𝒩₀ ℓ l, IsUnit (⟨h, hh⟩ : ↥(𝒩₀ ℓ l))) ∧ f * h = g) ∧
                  (∃ T : Finset (fieldBar q M'), Bx = Subring.closure
                    ({f : fieldBar q M' | ∃ c : AlgebraicClosure ℚ, c ∈ C' l ∧ f = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c} ∪
                      (↑T : Set (fieldBar q M'))))) ∧
                x ℓ ∈ 𝒩₀ ℓ l ∧ y ℓ ∈ 𝒩₀ ℓ l ∧ (∃ hu : u ℓ ∈ 𝒩₀ ℓ l, IsUnit (⟨u ℓ, hu⟩ : ↥(𝒩₀ ℓ l))) ∧
                ∃ (σ : Wc l →+* AdicCompletion (maximalIdeal ↥(𝒩₀ ℓ l)) ↥(𝒩₀ ℓ l))
                  (ι : AdicCompletion (maximalIdeal ↥(𝒩₀ ℓ l)) ↥(𝒩₀ ℓ l) ≃+* UVCrossingModel (Wc l) (π l ^ E l)),
                  (∀ h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ) ∈ 𝒩₀ ℓ l,
                    σ (π l) = algebraMap ↥(𝒩₀ ℓ l) (AdicCompletion (maximalIdeal ↥(𝒩₀ ℓ l)) ↥(𝒩₀ ℓ l)) ⟨_, h⟩) ∧
                  (∀ o : Wc l, ι (σ o) = const (π l ^ E l) o) ∧
                  (∀ (c : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (c : AlgebraicClosure ℚ) ∈ 𝒩₀ ℓ l),
                    ∃ o : Wc l, σ o = algebraMap ↥(𝒩₀ ℓ l) (AdicCompletion (maximalIdeal ↥(𝒩₀ ℓ l)) ↥(𝒩₀ ℓ l)) ⟨_, h⟩) ∧
                  (∀ (f : ↥(𝒩₀ ℓ l)) (n : ℕ) (h₁ : f.1 ∈ (𝒞.CIg ℓ).integers), (𝒞.CIg ℓ).residue ⟨f.1, h₁⟩ ≠ 0 →
                    (𝒞.xs ℓ s).ord ((𝒞.CIg ℓ).residue ⟨f.1, h₁⟩) = (n : ℤ) →
                      ∃ γ : UVCrossingModel (Wc l) (π l ^ E l), IsUnit γ ∧
                        ι (algebraMap ↥(𝒩₀ ℓ l) (AdicCompletion (maximalIdeal ↥(𝒩₀ ℓ l)) ↥(𝒩₀ ℓ l)) f) - γ * V (π l ^ E l) ^ n ∈
                          Ideal.span {const (π l ^ E l) (π l), U (π l ^ E l)}) ∧
                  (∀ (f : ↥(𝒩₀ ℓ l)) (n : ℕ) (h₂ : f.1 ∈ R.integers), R.residue ⟨f.1, h₂⟩ ≠ 0 →
                    (𝒞.xt ℓ s).ord (R.residue ⟨f.1, h₂⟩) = (n : ℤ) →
                      ∃ γ : UVCrossingModel (Wc l) (π l ^ E l), IsUnit γ ∧
                        ι (algebraMap ↥(𝒩₀ ℓ l) (AdicCompletion (maximalIdeal ↥(𝒩₀ ℓ l)) ↥(𝒩₀ ℓ l)) f) - γ * U (π l ^ E l) ^ n ∈
                          Ideal.span {const (π l ^ E l) (π l), V (π l ^ E l)}))))) :
    ∃ (M : AlgebraicCurve.SemistableModel A ↥(ModularCurve.FullLevel.fieldBar q M') 𝒞.sumFbar 𝒞.sumChart
          (fun e : CuspidalType.ProjLine q × ↥W => 𝒞.An e.1 e.2)
          (fun e => Sum.inl e.1) (fun e => Sum.inr e.2)
          (fun e => 𝒞.sumNode (Sum.inl e.1) e) (fun e => 𝒞.sumNode (Sum.inr e.2) e)),
      Nonempty M.Descent := by sorry
