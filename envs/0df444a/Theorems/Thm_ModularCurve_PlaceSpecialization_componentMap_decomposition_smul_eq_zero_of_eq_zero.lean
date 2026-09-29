-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_componentMap_decomposition_smul_eq_zero_of_eq_zero
-- name    : ModularCurve.PlaceSpecialization.componentMap_decomposition_smul_eq_zero_of_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/599387fb-8ba5-5457-a069-5680cdf7e488
-- title:
--   Decomposition-group stability of the kernel of the component map
-- statement:
--   Let $N$ be a non-zero natural number and $q$ a prime not dividing $N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, so that the residue field $k = \mathrm{ResidueField}\,A$ has characteristic $q$. Fix: a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,k\,N$ over $k$ whose members are exactly the supersingular places in the sense of `ssPlaces` (rational, affine geometric, with $j$-value in `ssJSet q k`); the hypothesis that the finite set $\mathrm{nodePairsOfPlaces}$ of pairs $(w, g\cdot w)$, $w \in W$, where $g = \mathrm{arithFrobC}\,q\,k\,N$ is the coefficientwise arithmetic Frobenius semilinear automorphism, is stable under $g$ acting on both coordinates; a modular polynomial datum `data` for $q$ satisfying the Kronecker congruence $\Phi \bmod q = (\mathbf{C}X^q - X)(\mathbf{C}X - X^q)$; integrality of the two degeneracy maps $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ at levels $N$, $q$ over $\overline{\mathbb{Q}}$; a place specialization $P$ for these data along the residue map $A \to k$; a width function $e$ on places; additive homomorphisms $\mathrm{comp}$ and $\mathrm{sp}$ from the inertia invariants of $\mathrm{JZero}(Nq)$ (degree-zero divisor classes of the base-changed modular function field of level $Nq$ fixed by the inertia subgroup of $A$ over $\mathbb{Q}$) to, respectively, the component group attached to the widths $\mathrm{widthOfPlaces}\,g\,W\,e$ (the dual of the character lattice modulo the image of the Gram map) and the glued Picard group $\mathrm{GluedPic0}$ for the above node pairs; surjectivity of $\mathrm{comp}$; the identification of the kernel, $\mathrm{comp}\,x = 0$ if and only if $x$ is a good class for the node pairs in the sense of $P$ (some degree-zero divisor $D$ with support consisting of strictly-first or strictly-second places, admissible glue datum, and class $x$); and the hypothesis that $\mathrm{sp}$ is a glued specialization for $P$. The conclusion: for every $\sigma$ in the decomposition subgroup of $A$ over $\mathbb{Q}$, every inertia-invariant class $x$ and every proof that $\sigma \cdot x$ is again inertia-invariant, $\mathrm{comp}\,x = 0$ implies that $\mathrm{comp}$ of $\sigma \cdot x$ is $0$ as well.
--
--   The statement expresses that the kernel of the map onto the component group of the special fibre at $q$ — the classes admitting a representative divisor compatible with the gluing of the two copies of the level-$N$ curve along the supersingular points — is stable under the whole decomposition group at $q$, not merely under inertia and Frobenius. It is one of the component clauses, stated for given witnesses, that are assembled in [`ModularCurve.exists_width_comp_sp`](thm.html#ModularCurve.exists_width_comp_sp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_componentMap_decomposition_smul_eq_zero_of_eq_zero.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.componentMap_decomposition_smul_eq_zero_of_eq_zero (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (hstab : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithFrobC q (ResidueField A) N))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (e : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) → ℕ)
      (comp : ↥(inertiaInvariants A (N * q)) →+
        componentGroup (widthOfPlaces (arithFrobC q (ResidueField A) N) W e))
      (sp : ↥(inertiaInvariants A (N * q)) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))
      (hsurj : Function.Surjective comp)
      (hker : ∀ x : ↥(inertiaInvariants A (N * q)),
        comp x = 0 ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (x : JZero (N * q)))
      (hsp : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) sp),
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ →
          ∀ (x : ↥(inertiaInvariants A (N * q)))
            (hx : σ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
            comp x = 0 → comp ⟨σ • (x : JZero (N * q)), hx⟩ = 0) := by sorry
