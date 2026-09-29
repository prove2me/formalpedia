-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_matrix_gluedSpecialization_nodeUnit_heckeGen_of_ne_of_isModel
-- name    : ModularCurve.PlaceSpecialization.exists_matrix_gluedSpecialization_nodeUnit_heckeGen_of_ne_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/7bff6a65-6059-5e18-83b7-b6d0afcd4e7f
-- title:
--   Hecke transport of node units on the glued fibre at q
-- statement:
--   Let $N \ge 1$ and let $q$ be a prime with $q \nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, so that $\kappa := \operatorname{ResidueField} A$ has characteristic $q$; the groups $\mathrm{JZero}(Nq)$ and $\mathrm{JZero}(N)$, the degree-zero divisor class groups of the base-changed modular function fields, carry the Hecke module structures `heckeModuleBar` over `HeckeAlg` $= \mathbb{Z}[X_\ell : \ell \text{ prime}]$. Fix: a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,\kappa\,N$ consisting exactly of the supersingular places `ssPlaces q N`; the node set $S := \mathrm{nodePairsOfPlaces}(g, W)$, the image of $W$ under $w \mapsto (w, g\cdot w)$ for $g$ the arithmetic Frobenius semilinear automorphism `arithFrobC q κ N`, assumed node-stable, i.e. $(g\cdot s_1, g\cdot s_2) \in S$ for all $s \in S$; modular polynomial data `data` for $q$ satisfying the Kronecker congruence $\Phi \equiv (Y^q - X)(Y - X^q) \bmod q$; integrality of the two degeneracy maps at levels $N, q$ over $\overline{\mathbb{Q}}$; a place-specialization datum $P$ at $A$ with residue map $\mathrm{residue}\,A$; a prolongation tuple $R$ for $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws) and `OrderLawFixed`; a width function $e$ on places; additive maps $\mathrm{comp}$ from the inertia invariants $H \subseteq \mathrm{JZero}(Nq)$ (the classes fixed by the inertia subgroup of $A$ over $\mathbb{Q}$) onto the component group of the widths $\mathrm{widthOfPlaces}(g, W, e)$, and $\mathrm{sp} : H \to \mathrm{GluedPic0}\,\kappa\,(\mathrm{modularFunctionFieldC}\,\kappa\,N)\,S$, with $\mathrm{comp}$ surjective, $\mathrm{comp}\,x = 0$ if and only if $x$ is a good class for $P$ relative to $S$, and $\mathrm{sp}$ a glued specialization for $P$ relative to $S$. Then for every prime $\ell \neq q$ there are an integer matrix $T$ indexed by $S \times S$ and an integer $n$ such that $\sum_t T_{t s} = n$ for every $s \in S$, and such that for every $x \in H$ with $X_\ell \cdot x$ again in $H$ and $\mathrm{comp}\,x = 0$, and every $w : S \to \mathrm{Additive}\,\kappa^{\times}$ with $\mathrm{sp}\,x = \mathrm{nodeUnit}_S(w)$, one has $\mathrm{sp}(X_\ell \cdot x) = \mathrm{nodeUnit}_S\bigl(t \mapsto \sum_s T_{s t} \cdot w_s\bigr)$.
--
--   This is the transport rule for the Hecke operator $T_\ell$, $\ell \neq q$, on the toric part of the glued special fibre at $q$ of the Jacobian of $X_0(Nq)$: good inertia-invariant classes whose glued specialization is a node unit vector are moved by an integral matrix on the nodes, and the equality of all column sums makes the image independent of the choice of representative unit vector, since constant vectors glue to zero. It feeds the construction of a semistable specialization datum for $\mathrm{JZero}(Nq)$ with its Néron and node clauses, which is the input to level lowering at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_matrix_gluedSpecialization_nodeUnit_heckeGen_of_ne_of_isModel.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_matrix_gluedSpecialization_nodeUnit_heckeGen_of_ne_of_isModel (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
      (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
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
        ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q →
          ∃ T : Matrix ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
              ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ℤ, ∃ n : ℤ,
            (∀ s, ∑ t, T t s = n) ∧
            ∀ (x : ↥(inertiaInvariants A (N * q)))
              (hx : heckeGen ℓ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
              comp x = 0 →
                ∀ w : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) →
                    Additive (ResidueField A)ˣ,
                  sp x = GluedPic0.nodeUnit
                      (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) w →
                    sp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩ =
                      GluedPic0.nodeUnit (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                        (fun t => ∑ s, T s t • w s) := by sorry
