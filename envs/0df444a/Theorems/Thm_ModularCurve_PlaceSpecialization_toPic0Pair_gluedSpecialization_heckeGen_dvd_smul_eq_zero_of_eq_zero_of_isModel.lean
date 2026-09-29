-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_toPic0Pair_gluedSpecialization_heckeGen_dvd_smul_eq_zero_of_eq_zero_of_isModel
-- name    : ModularCurve.PlaceSpecialization.toPic0Pair_gluedSpecialization_heckeGen_dvd_smul_eq_zero_of_eq_zero_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/61c921e7-7a86-5ad9-997a-3a31d562ab3a
-- title:
--   Hecke propagation of glued vanishing away from q
-- statement:
--   Let $N$ and $q$ be natural numbers with $N$ nonzero, $q$ prime and $q \nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$ is a nonunit of $A$; the residue field $k = \mathrm{ResidueField}\,A$ then has characteristic $q$, and both $J_0(Nq)$ and $J_0(N)$ — i.e. the degree-zero Picard groups $\mathrm{JZero}$ of the base-changed modular function fields — carry their Hecke-algebra module structures via `heckeModuleBar`. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,k\,N$ consisting exactly of the supersingular places `ssPlaces q N k`, assumed node-stable for the semilinear coefficient Frobenius $\mathrm{arithFrobC}\,q\,k\,N$ in the sense that the finite set $S$ of node pairs `nodePairsOfPlaces` attached to $W$ is preserved by the induced action; let `data` be modular polynomial data at $q$ satisfying the Kronecker congruence, and let $\mathrm{hα}$, $\mathrm{hβ}$ be integrality of the two degeneracy maps from level $N$ to level $Nq$. Let $P$ be a place specialization of level $N$ at $q$ with residue map $\mathrm{residue}\,A$, and $R$ a prolongation tuple for $P$ that is a model (the two divisor laws and the two cusp laws) and satisfies the regularity law and node value law for $W$ and the fixed-place order law. Let $e$ be a width function on places, let $\mathrm{comp}$ be a homomorphism from the inertia invariants of $J_0(Nq)$ (classes fixed by the inertia subgroup of $A$ over $\mathbb{Q}$) to the component group of the width data attached to $S$ and $e$, surjective and with $\mathrm{comp}\,x = 0$ if and only if the class $x$ is a good class for $S$ in the sense of $P$, and let $\mathrm{sp}$ be a homomorphism from those inertia invariants to $\mathrm{GluedPic0}\,k\,(\mathrm{modularFunctionFieldC}\,k\,N)\,S$ which is a glued specialization for $P$. The conclusion: for every prime $\ell$ dividing $N$ with $\ell \neq q$, and every inertia-invariant $x$ whose image $\mathrm{heckeGen}\,\ell \cdot x$ is again inertia-invariant, if $\mathrm{comp}\,x = 0$ and the image of $\mathrm{sp}\,x$ under $\mathrm{GluedPic0.toPic0Pair}$ (the pair of divisor classes of the two component divisors) vanishes, then the image of $\mathrm{sp}$ at $\mathrm{heckeGen}\,\ell \cdot x$ under $\mathrm{toPic0Pair}$ also vanishes.
--
--   This is the propagation step showing that the toric part of the glued specialization of a class in the inertia invariants of $J_0(Nq)$, once it vanishes, continues to vanish after applying the Hecke generator at a prime $\ell$ dividing $N$ and distinct from $q$; the mechanism is the commutation of the Hecke correspondence at $\ell$ with the two degeneracy reductions from level $Nq$ to level $N$ in characteristic $q$. It feeds the version for a general element of the Hecke algebra, [`ModularCurve.PlaceSpecialization.toPic0Pair_gluedSpecialization_heckeAlg_smul_eq_zero_of_eq_zero_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.toPic0Pair_gluedSpecialization_heckeAlg_smul_eq_zero_of_eq_zero_of_isModel), used in the level-lowering analysis at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_toPic0Pair_gluedSpecialization_heckeGen_dvd_smul_eq_zero_of_eq_zero_of_isModel.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.toPic0Pair_gluedSpecialization_heckeGen_dvd_smul_eq_zero_of_eq_zero_of_isModel (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ) (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
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
        (∀ ℓ : Nat.Primes, (ℓ : ℕ) ∣ N → (ℓ : ℕ) ≠ q →
          ∀ (x : ↥(inertiaInvariants A (N * q)))
            (hx : heckeGen ℓ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
            comp x = 0 →
              GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (sp x) = 0 →
                GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (sp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩) = 0) := by sorry
