-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_SemistableCovering_exists_node_forall_mem_annulus_dom_iff_of_charts_eq_smoothFibres_of_annulusFibre_of_nodeFibre
-- name    : ModularCurve.FullLevel.SemistableCovering.exists_node_forall_mem_annulus_dom_iff_of_charts_eq_smoothFibres_of_annulusFibre_of_nodeFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/e0fba790-9a2c-574b-8352-9a3a248812c8
-- title:
--   Annuli correspond bijectively to nodes of the special fibre
-- statement:
--   Fix a prime $q$ and $M'\neq 0$, a proper valuation subring $A\subseteq\overline{\mathbb Q}$ (its carrier is not all of $\overline{\mathbb Q}$) whose value group is archimedean in the sense that for $a,b\in A$ with $a$ in the maximal ideal and $b\neq0$ some power $a^{n}$ is divisible by $b$, a finite set $W$ of places of $\mathrm{modularFunctionFieldC}$ over the residue field of $A$, and a `SemistableCovering` $\mathcal C$ for $q,M',A,W$: charts $\mathcal C.\mathrm{CIg}\,\ell$ ($\ell$ in the projective line over $\mathbb Z/q$) and $\mathcal C.\mathrm{CSS}\,s$ ($s\in W$), annuli $\mathcal C.\mathrm{An}\,\ell\,s$ attached to them at the nodes $\mathcal C.\mathrm{xs}\,\ell\,s$, $\mathcal C.\mathrm{xt}\,\ell\,s$, and a partition of the places of $\mathrm{fieldBar}\,q\,M'$ into chart and annulus domains. Let $X\to\operatorname{Spec}A$ be integral, proper, flat and locally of finite presentation with all stalks integrally closed, together with an isomorphism $\varphi$ of $\mathrm{fieldBar}\,q\,M'$ with the function field of $X$ compatible with $A$. Assume, summarised: a specialisation dictionary $P\mapsto(\mathrm{pt}\,P,\mathrm{sp}\,P)$ (the local ring at $\mathrm{pt}\,P$ is $P$'s valuation ring, $\mathrm{pt}\,P$ lies over the generic point, $\mathrm{sp}\,P$ is the unique proper specialisation of $\mathrm{pt}\,P$, is closed, lies over the closed point, and the local ring at $\mathrm{sp}\,P$ sits inside $P$'s valuation ring with units detected by units of $A$ through $P.\mathrm{evalAt}$); generic points $\mathrm{gen}$ of the components indexed by the disjoint union of the two chart families, with local rings the chart integer rings, lying over the closed point and characterised among points of the special fibre by admitting a proper specialisation; node coordinates at every non-smooth closed point $x$ of the special fibre (exactly two components $\mathrm{gen}\,i$, $\mathrm{gen}\,j$ pass through $x$, and there are $t_1,t_2$ non-units at $x$, a unit $u$ and $\mu$ in the maximal ideal of $A$, nonzero, with $t_1t_2=\mu u$ and $t_k$ invertible on the corresponding component); the identification $\mathrm{hcharts}$ of chart domains with the locus where $\mathrm{sp}\,P$ is smooth; the hypothesis $\mathrm{hAnSp}$ that for each pair $(\ell,s)$ some non-smooth closed point $x$ of the special fibre receives both component generic points and receives every place of $\mathcal C.\mathrm{An}\,\ell\,s$; and $\mathrm{hNodeSp}$ that every non-smooth closed point of the special fibre is $\mathrm{sp}\,P$ for some place $P$. The conclusion has three parts: (i) for every $(\ell,s)$ there is a non-smooth closed point $x$ of the special fibre with $P\in(\mathcal C.\mathrm{An}\,\ell\,s).\mathrm{dom}$ if and only if $\mathrm{sp}\,P=x$, with $\mathrm{gen}(\mathrm{inl}\,\ell)\rightsquigarrow x$ and $\mathrm{gen}(\mathrm{inr}\,s)\rightsquigarrow x$, and with the branch readings that the chart residue of any element of $(\mathcal C.\mathrm{CIg}\,\ell).\mathrm{integers}$ (resp. $(\mathcal C.\mathrm{CSS}\,s).\mathrm{integers}$) lying in the local ring at $x$ belongs to the valuation ring of $\mathcal C.\mathrm{xs}\,\ell\,s$ (resp. $\mathcal C.\mathrm{xt}\,\ell\,s$); (ii) if places of $\mathcal C.\mathrm{An}\,\ell\,s$ and of $\mathcal C.\mathrm{An}\,\ell'\,s'$ have the same specialisation then $\ell=\ell'$ and $s=s'$; (iii) every non-smooth closed point $x$ of the special fibre is the common specialisation point of exactly one annulus, i.e. there are $\ell,s$ with $P\in(\mathcal C.\mathrm{An}\,\ell\,s).\mathrm{dom}\iff\mathrm{sp}\,P=x$.
--
--   This is the combinatorial matching step in the construction of a semistable model of the full-level modular curve over a valuation ring: the annuli of the rigid-analytic covering are put into bijection with the ordinary double points of the special fibre, each annulus meeting the Igusa component $\ell$ and the supersingular component $s$ in the prescribed attachment places. It feeds the descent statements that assemble a `SemistableModel` from the covering data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_SemistableCovering_exists_node_forall_mem_annulus_dom_iff_of_charts_eq_smoothFibres_of_annulusFibre_of_nodeFibre.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CategoryTheory AlgebraicGeometry

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.SemistableCovering.exists_node_forall_mem_annulus_dom_iff_of_charts_eq_smoothFibres_of_annulusFibre_of_nodeFibre
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : (A : Set (AlgebraicClosure ℚ)) ≠ Set.univ)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (𝒞 : SemistableCovering q M' A W)
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (φ : ↥(fieldBar q M') ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : AlgebraicClosure ℚ)) =
      SemistableModel.baseToFunctionField toBase a)

    (pt sp : Place (AlgebraicClosure ℚ) ↥(fieldBar q M') → X)
    (hpt : ∀ P, SemistableModel.localRing X φ (pt P) = P.toValuationSubring.toSubring ∧ (toBase.base (pt P)).asIdeal = ⊥)
    (hsp : ∀ P, pt P ⤳ sp P ∧ sp P ≠ pt P ∧ toBase.base (sp P) = closedPoint ↥A ∧ (∀ y : X, sp P ⤳ y → y = sp P) ∧
      (∀ y : X, pt P ⤳ y → y = pt P ∨ y = sp P) ∧
      ∀ f : ↥(fieldBar q M'), f ∈ SemistableModel.localRing X φ (sp P) →
        f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
          (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ (sp P), f * g = 1))

    (gen : CuspidalType.ProjLine q ⊕ ↥W → X)
    (hgenI : ∀ ℓ, SemistableModel.localRing X φ (gen (Sum.inl ℓ)) = (𝒞.CIg ℓ).integers.toSubring)
    (hgenS : ∀ s, SemistableModel.localRing X φ (gen (Sum.inr s)) = (𝒞.CSS s).integers.toSubring)
    (hgen_sp : ∀ i, toBase.base (gen i) = closedPoint ↥A)
    (hgen : ∀ x : X, toBase.base x = closedPoint ↥A → ((∃ i, x = gen i) ↔ ∃ y : X, x ⤳ y ∧ y ≠ x))

    (hnode : ∀ x : X, toBase.base x = closedPoint ↥A → (∀ y : X, x ⤳ y → y = x) → x ∉ toBase.smoothLocus →
      ∃ i j, i ≠ j ∧ gen i ⤳ x ∧ gen j ⤳ x ∧ (∀ k, gen k ⤳ x → k = i ∨ k = j) ∧
      ∃ (t₁ t₂ u u' : ↥(fieldBar q M')) (μ : ↥A), μ ∈ maximalIdeal ↥A ∧ (μ : AlgebraicClosure ℚ) ≠ 0 ∧
        t₁ ∈ SemistableModel.localRing X φ x ∧ t₂ ∈ SemistableModel.localRing X φ x ∧
        u ∈ SemistableModel.localRing X φ x ∧ u' ∈ SemistableModel.localRing X φ x ∧ u * u' = 1 ∧
        (¬ ∃ g ∈ SemistableModel.localRing X φ x, t₁ * g = 1) ∧ (¬ ∃ g ∈ SemistableModel.localRing X φ x, t₂ * g = 1) ∧
        t₁ * t₂ = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (μ : AlgebraicClosure ℚ) * u ∧

        (∃ g ∈ SemistableModel.localRing X φ (gen i), t₁ * g = 1) ∧ (∃ g ∈ SemistableModel.localRing X φ (gen j), t₂ * g = 1))

    (hcharts : ∀ P, ((∃ ℓ, P ∈ (𝒞.CIg ℓ).dom) ∨ ∃ s, P ∈ (𝒞.CSS s).dom) ↔ sp P ∈ toBase.smoothLocus)

    (hAnSp : ∀ (ℓ : CuspidalType.ProjLine q) (s : ↥W), ∃ x : X,
      x ∉ toBase.smoothLocus ∧ toBase.base x = closedPoint ↥A ∧ (∀ y : X, x ⤳ y → y = x) ∧
      gen (Sum.inl ℓ) ⤳ x ∧ gen (Sum.inr s) ⤳ x ∧ ∀ P, P ∈ (𝒞.An ℓ s).dom → sp P = x)

    (hNodeSp : ∀ x : X, toBase.base x = closedPoint ↥A → (∀ y : X, x ⤳ y → y = x) → x ∉ toBase.smoothLocus →
      ∃ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), sp P = x) :
    (∀ (ℓ : CuspidalType.ProjLine q) (s : ↥W), ∃ x : X,
      x ∉ toBase.smoothLocus ∧ toBase.base x = closedPoint ↥A ∧ (∀ y : X, x ⤳ y → y = x) ∧
      (∀ P, P ∈ (𝒞.An ℓ s).dom ↔ sp P = x) ∧
      gen (Sum.inl ℓ) ⤳ x ∧ gen (Sum.inr s) ⤳ x ∧

      (∀ (f : ↥(fieldBar q M')) (hf : f ∈ (𝒞.CIg ℓ).integers), f ∈ SemistableModel.localRing X φ x →
        (𝒞.CIg ℓ).residue ⟨f, hf⟩ ∈ (𝒞.xs ℓ s).toValuationSubring) ∧
      (∀ (f : ↥(fieldBar q M')) (hf : f ∈ (𝒞.CSS s).integers), f ∈ SemistableModel.localRing X φ x →
        (𝒞.CSS s).residue ⟨f, hf⟩ ∈ (𝒞.xt ℓ s).toValuationSubring)) ∧
    (∀ (ℓ ℓ' : CuspidalType.ProjLine q) (s s' : ↥W) (P P' : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')),
      P ∈ (𝒞.An ℓ s).dom → P' ∈ (𝒞.An ℓ' s').dom → sp P = sp P' → ℓ = ℓ' ∧ s = s') ∧
    (∀ x : X, toBase.base x = closedPoint ↥A → (∀ y : X, x ⤳ y → y = x) → x ∉ toBase.smoothLocus →
      ∃ ℓ s, ∀ P, P ∈ (𝒞.An ℓ s).dom ↔ sp P = x) := by sorry
