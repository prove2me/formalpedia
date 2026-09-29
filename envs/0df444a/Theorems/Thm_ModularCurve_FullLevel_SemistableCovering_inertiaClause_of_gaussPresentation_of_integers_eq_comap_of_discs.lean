-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_SemistableCovering_inertiaClause_of_gaussPresentation_of_integers_eq_comap_of_discs
-- name    : ModularCurve.FullLevel.SemistableCovering.inertiaClause_of_gaussPresentation_of_integers_eq_comap_of_discs
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/ed2ed60a-0e6e-55d5-bd83-4551219d84ac
-- title:
--   Inertia clause from Gauss presentation and residue discs
-- statement:
--   Let $q$ be a prime, $M'$ a nonzero natural number, $A$ a valuation subring of $\overline{\mathbb{Q}}$ and $W$ a finite set of places of $\mathrm{modularFunctionFieldC}$ over the residue field of $A$. Assume $q$ lies in the nonunits of $A$, that $q \nmid M'$, and fix $\pi \in \overline{\mathbb{Q}}$ with $\pi^{q^2-1} = q$, a semistable covering $\mathcal{C}$ of type `SemistableCovering q M' A W` (Igusa charts $\mathcal{C}.\mathrm{CIg}\,\ell$ indexed by $\ell \in \mathbb{P}^1(\mathbb{Z}/q)$, charts $\mathcal{C}.\mathrm{CSS}\,s$ indexed by $s \in W$, and annuli $\mathcal{C}.\mathrm{An}\,\ell\,s$, $\mathcal{C}.\mathrm{An}'\,\ell\,s$), and a primitive $q$-th root of unity $\zeta$. The hypotheses are: (i) $f$ lies in the valuation ring of the chart at `lineInfty q` exactly when $f\cdot y = x$ in $\overline{\mathbb{Q}}(\!(\mathfrak q)\!)$ for some Laurent series $x,y$ over $A$ with $y$ of nonzero coefficientwise reduction; (ii) for each $\ell$ there is $\gamma \in \Gamma_0(M')$ with the valuation ring of $\mathcal{C}.\mathrm{CIg}\,\ell$ the preimage of that of the chart at infinity under `levelAutBar q M' ζ γ`; (iii) for each Igusa chart and each chart indexed by $W$, the domain is the union of discs $\mathrm{disc}\,Q$ over $Q$ outside a finite set $N$, the place map sends $\mathrm{disc}\,Q$ to $Q$ and is constant off the domain, and each such disc is stable under the coefficientwise action of every $\tau$ in the inertia subgroup of $A$ over $\mathbb{Q}$ with $A.\mathrm{tameCharacter}\,\pi\,\tau = 1$; (iv) for each such $\tau$ and each $s$, that action induces an automorphism of the chart $\mathcal{C}.\mathrm{CSS}\,s$ inducing the identity on its reduced field; (v) for each such $\tau$, the action preserves each annulus domain and fixes the parameters of $\mathcal{C}.\mathrm{An}\,\ell\,s$ and $\mathcal{C}.\mathrm{An}'\,\ell\,s$. The conclusion is $\mathcal{C}.\mathrm{InertiaClause}\,\pi$: for every $\tau$ in the inertia subgroup of $A$ over $\mathbb{Q}$ with trivial tame character value at $\pi$, the semilinear automorphism $g$ given by $\tau$ acting coefficientwise preserves the valuation ring and residue map of every chart (with the identity on the reduced field), commutes with every place map, preserves every chart domain and every annulus domain, and fixes the parameters of all the annuli.
--
--   This is the inertia conjunct in the list of clauses required of a semistable covering of the full-level modular curve of level $q^2M'$ at a place above $q$: inertia of tame character $1$ acts trivially on the combinatorics of the covering (charts, reduction maps, annuli and their parameters). It is used in the assembly of a semistable covering together with all its clauses, in the three variants for general $q$ and for $q = 2, 3$ dividing the auxiliary level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_SemistableCovering_inertiaClause_of_gaussPresentation_of_integers_eq_comap_of_discs.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel AlgebraicCurve IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.SemistableCovering.inertiaClause_of_gaussPresentation_of_integers_eq_comap_of_discs
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
    (hA : A.LiesOverPrime q) (hqM' : ¬ q ∣ M')
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (𝒞 : SemistableCovering q M' A W) (ζ : Idx q)

    (hO : ∀ f : fieldBar q M', f ∈ (𝒞.CIg (lineInfty q)).integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hℓ : ∀ ℓ : CuspidalType.ProjLine q, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧
      (𝒞.CIg ℓ).integers = ((𝒞.CIg (lineInfty q)).integers).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)

    (hIg_discs : ∀ ℓ : CuspidalType.ProjLine q,
      ∃ (N : Finset (Place (ResidueField A) (𝒞.FIg ℓ)))
        (disc : Place (ResidueField A) (𝒞.FIg ℓ) → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
        (∀ P, P ∈ (𝒞.CIg ℓ).dom ↔ ∃ Q, Q ∉ N ∧ P ∈ disc Q) ∧
        (∀ P Q, Q ∉ N → P ∈ disc Q → (𝒞.CIg ℓ).placeMap P = Q) ∧
        (∀ P P', P ∉ (𝒞.CIg ℓ).dom → P' ∉ (𝒞.CIg ℓ).dom → (𝒞.CIg ℓ).placeMap P = (𝒞.CIg ℓ).placeMap P') ∧
        (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
          ∀ Q, Q ∉ N → ∀ P, P ∈ disc Q ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • P ∈ disc Q))

    (hSS_ind : ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
      ∀ s : ↥W, InducesOnChart (𝒞.CSS s) (ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ) (RingEquiv.refl _))
    (hSS_discs : ∀ s : ↥W,
      ∃ (N : Finset (Place (ResidueField A) (𝒞.FSS s)))
        (disc : Place (ResidueField A) (𝒞.FSS s) → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
        (∀ P, P ∈ (𝒞.CSS s).dom ↔ ∃ Q, Q ∉ N ∧ P ∈ disc Q) ∧
        (∀ P Q, Q ∉ N → P ∈ disc Q → (𝒞.CSS s).placeMap P = Q) ∧
        (∀ P P', P ∉ (𝒞.CSS s).dom → P' ∉ (𝒞.CSS s).dom → (𝒞.CSS s).placeMap P = (𝒞.CSS s).placeMap P') ∧
        (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
          ∀ Q, Q ∉ N → ∀ P, P ∈ disc Q ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • P ∈ disc Q))

    (hAn_dom : ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
      ∀ (ℓ : CuspidalType.ProjLine q) (s : ↥W) (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')),
        P ∈ (𝒞.An ℓ s).dom ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • P ∈ (𝒞.An ℓ s).dom)
    (hAn_param : ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
      ∀ (ℓ : CuspidalType.ProjLine q) (s : ↥W), ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (𝒞.An ℓ s).param = (𝒞.An ℓ s).param)
    (hAn'_param : ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
      ∀ (ℓ : CuspidalType.ProjLine q) (s : ↥W), ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (𝒞.An' ℓ s).param = (𝒞.An' ℓ s).param) :
    𝒞.InertiaClause π := by sorry
