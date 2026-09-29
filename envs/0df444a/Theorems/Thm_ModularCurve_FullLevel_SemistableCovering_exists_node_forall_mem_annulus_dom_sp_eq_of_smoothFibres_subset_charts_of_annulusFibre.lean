-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_SemistableCovering_exists_node_forall_mem_annulus_dom_sp_eq_of_smoothFibres_subset_charts_of_annulusFibre
-- name    : ModularCurve.FullLevel.SemistableCovering.exists_node_forall_mem_annulus_dom_sp_eq_of_smoothFibres_subset_charts_of_annulusFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/55eed6e7-1353-5df9-b082-cc949eb27b39
-- title:
--   Annulus nodes read by their attachment places
-- statement:
--   Fix a prime $q$, an integer $M'\neq 0$, and a valuation subring $A$ of $\overline{\mathbb Q}$ which is proper as a subset and of rank one in the sense that for all $a,b\in A$ with $a$ in the maximal ideal and $b\neq 0$ some power $a^n$ is divisible by $b$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}$ of level $M'$ over the residue field of $A$, and let $\mathcal C$ be a semistable covering of type `SemistableCovering q M' A W`, with Igusa charts $\mathcal C.\mathrm{CIg}\,\ell$ indexed by $\mathbb P^1(\mathbb F_q)$, supersingular charts $\mathcal C.\mathrm{CSS}\,s$ indexed by $W$, annuli $\mathcal C.\mathrm{An}\,\ell\,s$, and attachment places $\mathcal C.\mathrm{xs}\,\ell\,s$, $\mathcal C.\mathrm{xt}\,\ell\,s$ on the two charts. Let $X$ be an integral scheme with a proper, flat, locally of finite presentation morphism $\mathrm{toBase}$ to $\operatorname{Spec} A$, all of whose local rings are integrally closed, together with a ring isomorphism $\varphi$ from $\mathrm{fieldBar}\,q\,M'$ onto the function field of $X$ carrying the image of each $a\in A$ to the structural image of $a$ in the function field. The remaining hypotheses say that $X$ is a model of the covering in the following sense, the local ring $\mathrm{SemistableModel.localRing}\,X\,\varphi\,x$ being the subring of $\mathrm{fieldBar}\,q\,M'$ corresponding via $\varphi$ to the stalk at $x$: each place $P$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb Q}$ has a point $\mathrm{pt}\,P$ with local ring the valuation ring of $P$ and lying over the generic point of $\operatorname{Spec}A$, and a point $\mathrm{sp}\,P$ in its closure, distinct from it, closed, lying over the closed point of $\operatorname{Spec}A$, with $\mathrm{pt}\,P$ specialising only to itself and $\mathrm{sp}\,P$, and such that every $f$ in the local ring at $\mathrm{sp}\,P$ lies in the valuation ring of $P$, has $P.\mathrm{evalAt}\,f\in A$, and is invertible in that local ring exactly when $P.\mathrm{evalAt}\,f$ is a unit of $A$; a family $\mathrm{gen}$ indexed by $\mathbb P^1(\mathbb F_q)\sqcup W$ whose local rings are the chart rings $(\mathcal C.\mathrm{CIg}\,\ell).\mathrm{integers}$ and $(\mathcal C.\mathrm{CSS}\,s).\mathrm{integers}$, lying over the closed point of $\operatorname{Spec}A$, and exhausting the non-closed points of the fibre over the closed point; a node condition $\mathrm{hnode}$ saying that every closed point $x$ of that fibre outside the smooth locus of $\mathrm{toBase}$ lies in the closure of exactly two of the $\mathrm{gen}\,i$, say for $i\neq j$, and admits $t_1,t_2,u,u'$ in the local ring at $x$ and $\mu$ in the maximal ideal of $A$ with $\mu\neq 0$, $uu'=1$, $t_1$ and $t_2$ non-invertible there, $t_1t_2=\mu u$, while $t_1$ is invertible in the local ring at $\mathrm{gen}\,i$ and $t_2$ in that at $\mathrm{gen}\,j$; and finally the annulus-fibre hypothesis that for all $\ell$ and $s$ there is a closed point $x$ of the fibre, outside the smooth locus, in the closures of $\mathrm{gen}(\mathrm{inl}\,\ell)$ and $\mathrm{gen}(\mathrm{inr}\,s)$, with $\mathrm{sp}\,P=x$ for every $P$ in the domain of $\mathcal C.\mathrm{An}\,\ell\,s$. The conclusion is that for all $\ell$ and $s$ such a point $x$ may be chosen with the additional property that the chart residues are read by the attachment places: every $f$ in $(\mathcal C.\mathrm{CIg}\,\ell).\mathrm{integers}$ lying in the local ring at $x$ has residue in the valuation ring of $\mathcal C.\mathrm{xs}\,\ell\,s$, and every $f$ in $(\mathcal C.\mathrm{CSS}\,s).\mathrm{integers}$ lying in the local ring at $x$ has residue in the valuation ring of $\mathcal C.\mathrm{xt}\,\ell\,s$.
--
--   This is a step in the Bosch–Lütkebohmert style comparison between a semistable covering of the full-level modular function field by Igusa and supersingular charts joined by annuli, and a normal proper flat model over a rank-one valuation ring: it upgrades the bare localisation of an annulus domain in a single node fibre to the statement that the two charts meeting at that node induce their attachment places on it. It feeds the companion result identifying the fibre of an annulus domain with the set of places specialising to a prescribed node.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_SemistableCovering_exists_node_forall_mem_annulus_dom_sp_eq_of_smoothFibres_subset_charts_of_annulusFibre.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CategoryTheory AlgebraicGeometry

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.SemistableCovering.exists_node_forall_mem_annulus_dom_sp_eq_of_smoothFibres_subset_charts_of_annulusFibre
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

    (hAnSp : ∀ (ℓ : CuspidalType.ProjLine q) (s : ↥W), ∃ x : X,
      x ∉ toBase.smoothLocus ∧ toBase.base x = closedPoint ↥A ∧ (∀ y : X, x ⤳ y → y = x) ∧
      gen (Sum.inl ℓ) ⤳ x ∧ gen (Sum.inr s) ⤳ x ∧ ∀ P, P ∈ (𝒞.An ℓ s).dom → sp P = x) :
    ∀ (ℓ : CuspidalType.ProjLine q) (s : ↥W), ∃ x : X,
      x ∉ toBase.smoothLocus ∧ toBase.base x = closedPoint ↥A ∧ (∀ y : X, x ⤳ y → y = x) ∧
      (∀ P, P ∈ (𝒞.An ℓ s).dom → sp P = x) ∧
      gen (Sum.inl ℓ) ⤳ x ∧ gen (Sum.inr s) ⤳ x ∧
      (∀ (f : ↥(fieldBar q M')) (hf : f ∈ (𝒞.CIg ℓ).integers), f ∈ SemistableModel.localRing X φ x →
        (𝒞.CIg ℓ).residue ⟨f, hf⟩ ∈ (𝒞.xs ℓ s).toValuationSubring) ∧
      (∀ (f : ↥(fieldBar q M')) (hf : f ∈ (𝒞.CSS s).integers), f ∈ SemistableModel.localRing X φ x →
        (𝒞.CSS s).residue ⟨f, hf⟩ ∈ (𝒞.xt ℓ s).toValuationSubring) := by sorry
