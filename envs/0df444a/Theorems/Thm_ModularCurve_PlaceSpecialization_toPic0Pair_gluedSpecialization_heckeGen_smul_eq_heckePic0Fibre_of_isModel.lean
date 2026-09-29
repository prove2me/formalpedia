-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_toPic0Pair_gluedSpecialization_heckeGen_smul_eq_heckePic0Fibre_of_isModel
-- name    : ModularCurve.PlaceSpecialization.toPic0Pair_gluedSpecialization_heckeGen_smul_eq_heckePic0Fibre_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/0258c213-9d32-5ac0-9197-1937c66513e0
-- title:
--   Hecke law for the glued specialization on Pic⁰ pairs
-- statement:
--   Fix $N \ge 1$ and a prime $q$ with $q \nmid N$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ such that $q$ lies in the nonunits of $A$, so that the residue field $k = \mathrm{ResidueField}(A)$ has characteristic $q$; the groups $\mathrm{JZero}(Nq)$ and $\mathrm{JZero}(N)$, namely the degree-zero divisor class groups of the base-changed modular function fields of levels $Nq$ and $N$ over $\overline{\mathbb{Q}}$, carry the `heckeModuleBar` module structure over $\mathrm{HeckeAlg} = \mathbb{Z}[X_\ell : \ell \text{ prime}]$, in which `heckeGen` $\ell = X_\ell$ acts by the level-$N$ or level-$Nq$ Hecke operator. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,k\,N$ consisting exactly of the supersingular places `ssPlaces` $q\,N\,k$, such that the node set $S = \{(w, \sigma \cdot w) : w \in W\}$, formed with the coefficient Frobenius semilinear automorphism $\sigma = \mathrm{arithFrobC}\,q\,k\,N$, is stable under $\sigma$; let `data` be a modular polynomial datum for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ killing $(j, j_q)$) satisfying the Kronecker congruence modulo $q$, let $h\alpha$, $h\beta$ assert integrality of the two degeneracy inclusions of level $N$ into level $Nq$, let $P$ be a place specialization for these data over the residue map $A \to k$, and let $R$ be a prolongation tuple over $P$ satisfying the model law (the two divisor laws and the cusp laws at $\infty$ and $0$), the regularity and node-value laws on $W$, and the fixed-place order law. Let $e$ assign a width to each place, let `comp` be an additive map from the inertia invariants of $\mathrm{JZero}(Nq)$ (the elements fixed by the inertia subgroup of $A$ over $\mathbb{Q}$) onto the component group of the width function $s \mapsto e(s_1)$ on $S$, whose kernel consists exactly of the classes that are good for $S$ in the sense of $P$, and let `sp` be an additive map from those inertia invariants to $\mathrm{GluedPic0}\,k\,(\mathrm{modularFunctionFieldC}\,k\,N)\,S$ which is a glued specialization for $P$ and $S$. Then for every prime $\ell \nmid Nq$, every inertia-invariant $x$ with $X_\ell \cdot x$ again inertia invariant and $\mathrm{comp}(x) = 0$, and assuming the fibre Hecke inputs `HeckeInputsFibre` $k\,N\,\ell$ hold, the pair of divisor classes $\mathrm{toPic0Pair}(\mathrm{sp}(X_\ell \cdot x))$ equals the pair obtained by applying the fibre Hecke operator $\mathrm{heckePic0Fibre}\,k\,N\,\ell$ to each of the two components of $\mathrm{toPic0Pair}(\mathrm{sp}(x))$.
--
--   This is the Hecke-compatibility clause of the semistable-reduction package for $J_0(Nq)$ at $q$: it says that the glued specialization map, read through its two $\mathrm{Pic}^0$ components, intertwines the Hecke operator at a prime $\ell \nmid Nq$ upstairs with the corresponding correspondence operator on the special fibre of level $N$. It is one of the clauses bound together with the existence of the widths, the component map and the glued specialization, and is used by [`ModularCurve.exists_width_comp_sp`](thm.html#ModularCurve.exists_width_comp_sp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_toPic0Pair_gluedSpecialization_heckeGen_smul_eq_heckePic0Fibre_of_isModel.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.toPic0Pair_gluedSpecialization_heckeGen_smul_eq_heckePic0Fibre_of_isModel (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
        (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N * q →
          ∀ (x : ↥(inertiaInvariants A (N * q)))
            (hx : heckeGen ℓ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
            comp x = 0 →
              haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
              HeckeInputsFibre (ResidueField A) N ℓ →
                GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                    (sp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩) =
                  (heckePic0Fibre (ResidueField A) N ℓ
                      (GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                        (sp x)).1,
                    heckePic0Fibre (ResidueField A) N ℓ
                      (GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                        (sp x)).2)) := by sorry
