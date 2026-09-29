-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_good_admissible_rep_heckeDivBar_good_admissible_kindResp_of_isModel
-- name    : ModularCurve.PlaceSpecialization.exists_good_admissible_rep_heckeDivBar_good_admissible_kindResp_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/bf0c3883-1028-5687-8964-80f3a4bbaabb
-- title:
--   Kind-respecting good admissible representative for T_ℓ on J₀(Nq)
-- statement:
--   Fix an integer $N \ge 1$ and a prime $q$ with $q \nmid N$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ in which $q$ is a non-unit, so that its residue field $k = \mathrm{ResidueField}\ A$ has characteristic $q$. Let $W$ be a finite set of places of `modularFunctionFieldC k N` over $k$ whose elements are exactly the supersingular places, i.e. the rational places $w$ at which the two generators $j$, $j_N$ both lie in the valuation ring and at which the value of the geometric generator lies in `ssJSet q`. Let `data` consist of a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$, subject to the Kronecker congruence $\Phi \equiv (Y^{q} - X)(Y - X^{q}) \pmod q$, and assume that the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$ are integral. Let $P$ be a `PlaceSpecialization` for these data — a map `sp` from places of the level-$N$ function field over $\overline{\mathbb{Q}}$ to places of `modularFunctionFieldC k N`, a homomorphism on degree-zero divisor classes, and the compatibility conditions of that structure — and let $R$ be a `ProlongationTuple` for $P$ satisfying `IsModel` (the two divisor laws together with the cusp laws at $\infty$ and at $0$), the regularity law and the node-value law for $W$, and the fixed-place order law. Write $S$ for the finite set of node pairs $(w, \sigma \cdot w)$, $w \in W$, where $\sigma$ is the arithmetic Frobenius semilinear automorphism `arithFrobC q k N`. The conclusion is: for every prime $\ell \ne q$, assuming the two degeneracy embeddings from level $Nq$ to level $Nq\ell$ are integral and that the level-$Nq\ell$ function field over $\overline{\mathbb{Q}}$ has principal divisors, every class $x \in \mathrm{Pic}^0$ of the level-$Nq$ function field over $\overline{\mathbb{Q}}$ that is $P$-good for $S$ admits a degree-zero divisor $D$ with $\mathrm{Pic}^0$-class $x$ such that $D$ is good (each place in its support is strictly of the first kind, $\mathrm{Frob}(\mathrm{reduceFst}\ V) = \mathrm{reduceSnd}\ V$ with $\mathrm{Frob}^2(\mathrm{reduceFst}\ V) \ne \mathrm{reduceFst}\ V$, or strictly of the second kind, symmetrically), its gluing datum `P.glueData S D` is admissible (both component divisors have degree zero and vanish at the first, respectively second, coordinates of the pairs in $S$), and in addition the Hecke correspondence `heckeDivBar hαℓ hβℓ` at $\ell$ (pullback along the second degeneracy map followed by pushforward along the first) carries $D$ to a good divisor with admissible gluing datum, and commutes with the passage to the strictly-first-kind and strictly-second-kind parts of $D$.
--
--   This is the moving lemma for a prime $\ell$ distinct from $q$ on the level-$Nq$ curve at a place over $q$: within a $P$-good divisor class one may choose a representative which, together with its $\ell$-Hecke translate, is good with admissible gluing datum and whose two kind-parts are respected by the translate, the geometric background being the Deligne–Rapoport description of the special fibre at $q$ as two copies of the level-$N$ curve crossing at the supersingular points. It is used in the comparison of the Hecke correspondence at $\ell$ with its counterpart on the glued Picard group, in particular in the results giving a matrix description of that action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_good_admissible_rep_heckeDivBar_good_admissible_kindResp_of_isModel.lean

import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.exists_good_admissible_rep_heckeDivBar_good_admissible_kindResp_of_isModel
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ) (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed),
        (∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q →
          haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
          ∀ (hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
            (hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
            [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar ((N * q) * ℓ))],
          ∀ (x : JZero (N * q)),
            P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) x →
              ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                  (F := ↥(modularFunctionFieldBar (N * q)))),
                P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧
                P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) D
                  ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ∧
                Pic0.mk D = x ∧
                P.IsGoodDiv (heckeDivBar hαℓ hβℓ
                  (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) ∧
                P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                    (heckeDivBar hαℓ hβℓ
                      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
                  ∈ GluingData.admissible
                      (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ∧
                P.fstDiv (heckeDivBar hαℓ hβℓ
                    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
                  = heckeDivBar hαℓ hβℓ (P.fstDiv
                      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) ∧
                P.sndDiv (heckeDivBar hαℓ hβℓ
                    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
                  = heckeDivBar hαℓ hβℓ (P.sndDiv
                      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))) := by sorry
