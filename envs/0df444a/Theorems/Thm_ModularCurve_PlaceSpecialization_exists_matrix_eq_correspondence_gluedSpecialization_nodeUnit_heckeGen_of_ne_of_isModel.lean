-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_matrix_eq_correspondence_gluedSpecialization_nodeUnit_heckeGen_of_ne_of_isModel
-- name    : ModularCurve.PlaceSpecialization.exists_matrix_eq_correspondence_gluedSpecialization_nodeUnit_heckeGen_of_ne_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/60583995-6118-5ef2-9554-137ce7b7e226
-- title:
--   Hecke transport of node units on the glued fibre at q
-- statement:
--   Let $N\ge 1$ and let $q$ be a prime not dividing $N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ (that is, $q$ is a non-unit of $A$), so that its residue field $\kappa=\mathrm{ResidueField}\,A$ has characteristic $q$; the groups $\mathrm{JZero}(Nq)=\mathrm{Pic}^0$ of the base-changed modular function field at level $Nq$ and $\mathrm{JZero}(N)$ carry their Hecke-algebra module structures, $\mathrm{HeckeAlg}=\mathbb{Z}[X_\ell]$ over the primes. Fix: a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,\kappa\,N$ consisting exactly of the supersingular places `ssPlaces q N κ`; the node set $S=$ `nodePairsOfPlaces (arithFrobC q κ N) W`, the image of $W$ under the pair embedding attached to the coefficientwise $q$-power Frobenius semilinear automorphism $\mathrm{arithFrobC}$, assumed stable under that automorphism in the sense that $(g\cdot s_1,g\cdot s_2)\in S$ for all $s\in S$; modular-polynomial data `data` for $q$ satisfying the Kronecker congruence $\overline{\Phi}=(X'^q-X)(X'-X^q)$; integrality of the two level-$q$ degeneracy maps over $\overline{\mathbb{Q}}$ ($h\alpha$, $h\beta$); a place-specialization datum $P$ at $A$ for level $N$ and $q$ with reduction $\mathrm{residue}\,A$ into $\kappa$; a prolongation tuple $R$ for $P$ which is a model (its two divisor laws and its two cusp laws hold) and satisfies `OrderLawFixed`; a width function $e$ on places; additive maps $\mathrm{comp}$ from the inertia invariants $H=\mathrm{inertiaInvariants}\,A\,(Nq)\subseteq \mathrm{JZero}(Nq)$ (the elements fixed by the inertia subgroup of $A$ over $\mathbb{Q}$) onto the component group of the width function `widthOfPlaces (arithFrobC q κ N) W e`, assumed surjective and with $\mathrm{comp}\,x=0$ exactly when $x$ is a good class for $P$ relative to $S$, and $\mathrm{sp}:H\to \mathrm{GluedPic}^0(\kappa,\mathrm{modularFunctionFieldC}\,\kappa\,N,S)$ which is a glued specialization for $P$. Then for every prime $\ell\ne q$ there exist an integer matrix $T$ indexed by $S\times S$ and an integer $n$ such that: every column sum of $T$ equals $n$, i.e. $\sum_t T_{t s}=n$ for all $s$; $n$ is `finrankAlong` of the first degeneracy inclusion $\mathrm{heckeAlphaC}\,\kappa\,N\,\ell$, the degree of $\mathrm{charLDegeneracyRoof}\,\kappa\,N\,\ell$ over $\mathrm{modularFunctionFieldC}\,\kappa\,N$ along that inclusion; under the further assumptions that the roof has principal divisors and that both $\mathrm{heckeAlphaC}$ and $\mathrm{heckeBetaC}$ at level $N$ and prime $\ell$ are integral, $T_{st}$ equals the value at the place underlying $s$ of the divisor correspondence (pullback along $\mathrm{heckeAlphaC}$ followed by pushforward along $\mathrm{heckeBetaC}$) applied to the divisor $1\cdot$(place underlying $t$); and, for every $x\in H$ with $X_\ell\cdot x$ again in $H$ and $\mathrm{comp}\,x=0$, and every family $w$ of elements of $\mathrm{Additive}\,\kappa^\times$ indexed by $S$ with $\mathrm{sp}\,x=\mathrm{nodeUnit}\,w$, one has $\mathrm{sp}(X_\ell\cdot x)=\mathrm{nodeUnit}\bigl(t\mapsto \sum_s T_{st}\cdot w_s\bigr)$.
--
--   This is the transport of the Hecke operator $T_\ell$, $\ell\neq q$, across the Deligne–Rapoport description of the fibre at $q$ of the modular curve of level $Nq$ as two copies of the level-$N$ curve crossing at the supersingular points: on the torus part of the glued $\mathrm{Pic}^0$, i.e. on classes represented by node units, $T_\ell$ acts through an integer matrix on the nodes whose entries are the Hecke correspondence on supersingular places and whose column sums are the degree of the first degeneracy map. It feeds the companion statement comparing this action with the action on the component group, and the Čerednik–Drinfeld-style two-level specialization results used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_matrix_eq_correspondence_gluedSpecialization_nodeUnit_heckeGen_of_ne_of_isModel.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_CharLDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open IsLocalRing ModularCurve
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.exists_matrix_eq_correspondence_gluedSpecialization_nodeUnit_heckeGen_of_ne_of_isModel
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
            (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩;
              n = (finrankAlong (ResidueField A) (heckeAlphaC (ResidueField A) N ℓ) : ℤ)) ∧
            (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩;
              ∀ [HasPrincipalDivisors (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ)]
                (hαc : HeckeAlphaCIntegral (ResidueField A) N ℓ) (hβc : HeckeBetaCIntegral (ResidueField A) N ℓ)
                (s t : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)),
                T s t = Divisor.correspondence (heckeAlphaC (ResidueField A) N ℓ)
                  (heckeBetaC (ResidueField A) N ℓ) hαc hβc (Finsupp.single t.1.1 1) s.1.1) ∧
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
