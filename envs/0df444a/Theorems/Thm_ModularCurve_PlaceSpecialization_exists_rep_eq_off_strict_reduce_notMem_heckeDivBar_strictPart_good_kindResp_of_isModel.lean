-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_rep_eq_off_strict_reduce_notMem_heckeDivBar_strictPart_good_kindResp_of_isModel
-- name    : ModularCurve.PlaceSpecialization.exists_rep_eq_off_strict_reduce_notMem_heckeDivBar_strictPart_good_kindResp_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/200af41f-1a40-5344-9f1a-08f083366e70
-- title:
--   Moving the strict part of a divisor off T₀, kind-respecting
-- statement:
--   Let $N\ge 1$ and let $q$ be a prime not dividing $N$; let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, so that $\kappa:=\mathrm{ResidueField}\,A$ has characteristic $q$. Assume given: a finite set $W$ of places of $\kappa(\,\overline{j},\overline{j}_N\,)=$ `modularFunctionFieldC` $\kappa\,N$ whose members are exactly the supersingular places (rational, affine geometric, with value of the generator $j$ in the supersingular $j$-set for $q$); modular polynomial data `data` at $q$ satisfying the Kronecker congruence $\Phi \bmod q=(C X^q-X)(C X-X^q)$; integrality $h\alpha,h\beta$ of the two degeneracy embeddings from level $N$ to level $Nq$ over $\overline{\mathbb Q}$; a place specialisation $P$ for these data with residue map $A\to\kappa$; and a prolongation tuple $R$ over $P$ which is a model (the two divisor laws and the two cusp laws), satisfies the regularity law and the node-value law at $W$, and satisfies the order law at Frobenius-fixed places. Then for every prime $\ell\neq q$, every integrality data $h\alpha_\ell,h\beta_\ell$ for $\ell$ at level $Nq$ (with principal divisors available at level $Nq\ell$), every finite set $T_0$ of places of `modularFunctionFieldC` $\kappa\,N$, and every degree-zero divisor $D$ on `modularFunctionFieldBar` $(Nq)$, there is a degree-zero divisor $D_1$ such that: $D_1$ and $D$ have the same class in $\mathrm{Pic}^0$; $D_1(V)=D(V)$ at every place $V$ which is strict of neither kind, where $V$ is strict of the first kind when $\mathrm{Frob}(P.\mathrm{reduceFst}\,V)=P.\mathrm{reduceSnd}\,V$ and $\mathrm{Frob}^2(P.\mathrm{reduceFst}\,V)\neq P.\mathrm{reduceFst}\,V$, and strict of the second kind when $P.\mathrm{reduceFst}\,V=\mathrm{Frob}(P.\mathrm{reduceSnd}\,V)$ and $\mathrm{Frob}^2(P.\mathrm{reduceSnd}\,V)\neq P.\mathrm{reduceSnd}\,V$; every strict place in the support of $D_1$ has both reductions $P.\mathrm{reduceFst}\,V$ and $P.\mathrm{reduceSnd}\,V$ outside $T_0$; and, writing $T_\ell=$ `heckeDivBar` $h\alpha_\ell\,h\beta_\ell$ and $E\mapsto E^{(1)},E^{(2)}$ for the restrictions of a divisor to the places strict of the first, resp. second, kind, the divisor $T_\ell(D_1^{(1)}+D_1^{(2)})$ is supported on strict places and satisfies $\bigl(T_\ell(D_1^{(1)}+D_1^{(2)})\bigr)^{(1)}=T_\ell(D_1^{(1)})$ and $\bigl(T_\ell(D_1^{(1)}+D_1^{(2)})\bigr)^{(2)}=T_\ell(D_1^{(2)})$.
--
--   This is the unrestricted form of the kind-respecting moving lemma on $X_0(Nq)$: an arbitrary degree-zero divisor class is represented by a divisor whose non-strict coefficients are unchanged, whose strict points reduce outside a prescribed finite set of places of the level-$N$ fibre, and whose strict part is carried by the $\ell$-th Hecke correspondence into strict places compatibly with the splitting into the two kinds. It is used in the computation of the action of Hecke generators on the component group via the depth pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_rep_eq_off_strict_reduce_notMem_heckeDivBar_strictPart_good_kindResp_of_isModel.lean

import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.exists_rep_eq_off_strict_reduce_notMem_heckeDivBar_strictPart_good_kindResp_of_isModel
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
          ∀ (T₀ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
            (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
              (F := ↥(modularFunctionFieldBar (N * q))))),
              ∃ D₁ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                  (F := ↥(modularFunctionFieldBar (N * q)))),

                Pic0.mk D₁ = Pic0.mk D ∧

                (∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
                  ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V) →
                    (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) V = (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) V) ∧

                (∀ V ∈ (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
                  (P.IsStrictFst V ∨ P.IsStrictSnd V) → P.reduceFst V ∉ T₀ ∧ P.reduceSnd V ∉ T₀) ∧

                P.IsGoodDiv (heckeDivBar hαℓ hβℓ
                  (P.fstDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) + P.sndDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))) ∧
                P.fstDiv (heckeDivBar hαℓ hβℓ
                    (P.fstDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) + P.sndDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))))
                  = heckeDivBar hαℓ hβℓ (P.fstDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) ∧
                P.sndDiv (heckeDivBar hαℓ hβℓ
                    (P.fstDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) + P.sndDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))))
                  = heckeDivBar hαℓ hβℓ (P.sndDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))) := by sorry
