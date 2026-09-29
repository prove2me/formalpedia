-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_saturated_of_sp_eq_spPlace_residueField
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue_saturated_of_sp_eq_spPlace_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/6ab95892-802d-5a13-a85a-1df9dbbfb8bf
-- title:
--   Saturation of the two node residues at a supersingular place
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ whose residue field $\kappa_A =$ `IsLocalRing.ResidueField A` has characteristic $q$, and a level $N \geq 1$ with $q \nmid N$. The standing data are: `data`, a modular polynomial datum of level $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions) together with the Kronecker congruence `hKr` asserting $\Phi \equiv (C(X)^q - X)(C(X) - X^q)$ after reduction modulo $q$; integrality hypotheses `hα`, `hβ` for the two degeneracy maps from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$, namely the inclusion of full modular function fields and the $\mathfrak{q} \mapsto \mathfrak{q}^q$ substitution; a fibre model `fm` of level $N$ over $A$ with reduction `IsLocalRing.residue A : A → \kappa_A`; modular polynomial data `dataAll d` for every $d \mid N$, with `hsep` asserting that the level-$N$ polynomial, reduced to $\kappa_A$ and viewed in $\mathrm{RatFunc}(\kappa_A)[Y]$, is separable. Let $P$ be a place specialization for these data, valued in places of $\mathrm{modularFunctionFieldC}\,\kappa_A\,N$, whose specialization map `P.sp` is the one `fm.spPlace` attached to `fm` (hypothesis `hP`), and let $R$ be a prolongation tuple over $P$ satisfying the fixed-place order law `R.OrderLawFixed`. Let $w$ be a supersingular place of $\mathrm{modularFunctionFieldC}\,\kappa_A\,N$, i.e. $w$ is rational, both $j$ and $j_N$ lie in its valuation subring, and the value of $j$ at $w$ is a supersingular $j$-invariant. Let $K$ be a finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ and write $O_K = A \cap K$ for the coefficient subring `NodeLocalized.coeffSubring A K`; let $\mathcal{O} = R.\mathrm{nodeIntegersOver}\,K\,w$ be the ring of those $f$ in the level-$Nq$ function field over $\overline{\mathbb{Q}}$ that lie in the integers of both prolongations $R_1$, $R_2$, in the valuation subring of every place $V$ with `P.reduceFst V = w`, and whose Laurent expansion lies in the subfield generated over $K$ by the constants and the two $j$-expansions. Assume `hres`: every $g \in \mathcal{O}$ admits $o \in O_K$ with $g - \mathrm{nodeConst}_K^w(o)$ a non-unit. The conclusion is threefold. First, for $g, g' \in \mathcal{O}$, if $w.\mathrm{ord}$ of the first node residue of $g$ is positive and that of $g'$ equals $1$, then the first node residue of $g$ is the product of that of $g'$ with that of some $b \in \mathcal{O}$. Second, the same holds for the second node residue with respect to the place $\mathrm{arithFrob}_q \cdot w$, the translate of $w$ under the semilinear automorphism induced by the $q$-power Frobenius of $\kappa_A$. Third, for every $\varpi \in O_K$ generating the kernel of the reduction $O_K \to \kappa_A$, in the sense that $d$ reduces to $0$ if and only if $d \in \varpi O_K$, every $g \in \mathcal{O}$ whose two node residues both vanish is of the form $\mathrm{nodeConst}_K^w(\varpi) \cdot b$ with $b \in \mathcal{O}$.
--
--   This is the saturation statement for the local ring of a supersingular node on the level-$Nq$ modular curve in characteristic $q$: the values of each of the two branch reductions are divisible by any value of order one, and an element vanishing along both branches is divisible by a uniformiser of the coefficient ring. It is specialised to the residue field of $A$ itself, the specialisation map being pinned down by the fibre model via `hP`, and is used in the two `nodePack_residueField_of_…` results that package the node data over that residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_saturated_of_sp_eq_spPlace_residueField.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ValuationSubring_ReduceAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open AlgebraicCurve ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem
ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue_saturated_of_sp_eq_spPlace_residueField
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    [CharP (IsLocalRing.ResidueField ↥A) q]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] (hqN : ¬ q ∣ N)
    (fm : CharPModel.FibreModel N A q (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField ↥A)))).map
      (algebraMap (Polynomial (IsLocalRing.ResidueField ↥A)) (RatFunc (IsLocalRing.ResidueField ↥A)))).Separable)
    (P : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
    (hP : P.sp = fm.spPlace IsLocalRing.residue_surjective dataAll hsep)
    (R : ProlongationTuple P) (hO : R.OrderLawFixed)
    (w : Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N))
    (hw : w ∈ ssPlaces q N (IsLocalRing.ResidueField ↥A))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hres : ∀ g : ↥(R.nodeIntegersOver K w),
      ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o)) :
    (∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.nodeResidue₁ w ⟨g', g'.2.1⟩ * R.nodeResidue₁ w ⟨b, b.2.1⟩) ∧
    (∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < (arithFrobC q (IsLocalRing.ResidueField ↥A) N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) →
      (arithFrobC q (IsLocalRing.ResidueField ↥A) N • w).ord (R.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.nodeResidue₂ w ⟨g', g'.2.1⟩ * R.nodeResidue₂ w ⟨b, b.2.1⟩) ∧
    (∀ ϖ : ↥(NodeLocalized.coeffSubring A K),
      (∀ d : ↥(NodeLocalized.coeffSubring A K),
        NodeLocalized.redRestrict (IsLocalRing.residue ↥A) K d = 0 ↔ ∃ d', d = ϖ * d') →
      ∀ g : ↥(R.nodeIntegersOver K w), R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 → R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0 →
        ∃ b : ↥(R.nodeIntegersOver K w), g = R.nodeConst K w ϖ * b) := by sorry
