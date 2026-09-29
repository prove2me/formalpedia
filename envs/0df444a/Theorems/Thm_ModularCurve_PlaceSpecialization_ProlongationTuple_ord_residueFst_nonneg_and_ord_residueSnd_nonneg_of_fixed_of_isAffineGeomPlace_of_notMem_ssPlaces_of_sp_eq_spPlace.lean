-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_and_ord_residueSnd_nonneg_of_fixed_of_isAffineGeomPlace_of_notMem_ssPlaces_of_sp_eq_spPlace
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_nonneg_and_ord_residueSnd_nonneg_of_fixed_of_isAffineGeomPlace_of_notMem_ssPlaces_of_sp_eq_spPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/46955841-72f6-5e6a-8485-6a3b260baf57
-- title:
--   Both residues regular at a Frobenius-square-fixed ordinary affine place
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a nonzero level $N$, a field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} : A \to k$, modular polynomial data `data` at $q$ (a monic bivariate integral polynomial $\Phi$ of degree $\psi(q)$ vanishing on the pair $(j,j_q)$) satisfying the Kronecker congruence $\Phi \equiv (Y^q - X)(Y - X^q)$ modulo $q$, and integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of level $(N,q)$ over $\overline{\mathbb{Q}}$. Assume $q \nmid N$, let `fm` be a fibre model of level $N$ over $A$ relative to $\mathrm{red}$, let $\mathrm{red}$ be surjective, let `dataAll` assign modular polynomial data to every divisor $d \mid N$, and let `hsep` assert that the level-$N$ polynomial $\Phi_N$, reduced into $k$ and viewed over $\mathrm{RatFunc}\,k$, is separable. Let $P$ be a place specialisation of level $N$ at $q$ whose map on places `P.sp` equals the specialisation map `fm.spPlace hred dataAll hsep` of the fibre model, and let $R$ be a prolongation tuple over $P$, with regular prolongations $R.R_1$, $R.R_2$ of the level-$Nq$ field $\overline{\mathbb{Q}}(X_0(Nq))$ = `modularFunctionFieldBar (N * q)` and associated residue maps `R.residue₁`, `R.residue₂` taking values in the function field `modularFunctionFieldC k N` of the level-$N$ curve over $k$. The conclusion is: for every $f$ in `modularFunctionFieldBar (N * q)` lying in the integers of both $R.R_1$ and $R.R_2$, and every place $v$ of `modularFunctionFieldC k N` over $k$ such that (i) $v$ is fixed by the square of the geometric Frobenius `frobOnPlacesGeomLevel k N data hKr`, (ii) $v$ is affine, i.e. both generators `jGeomGen k N` and `jNGeomGen k N` lie in the valuation subring of $v$, (iii) $v$ is not a supersingular place, i.e. $v \notin$ `ssPlaces q N k`, and (iv) $\mathrm{ord}_V(f) \ge 0$ for every place $V$ of `modularFunctionFieldBar (N * q)` whose first reduction `P.reduceFst V` (the specialisation under `P.sp` of the restriction of $V$ along `heckeAlphaBar`) is $v$, one has: if `R.residue₁ ⟨f, h₁⟩` is nonzero then its order at $v$ is $\ge 0$, and if `R.residue₂ ⟨f, h₂⟩` is nonzero then its order at the Frobenius image `frobOnPlacesGeomLevel k N data hKr v` is $\ge 0$.
--
--   This is the regularity half of the dictionary between the two components of the special fibre of $X_0(Nq)$ at $q$ and the two residues of a prolongation tuple: at an ordinary (non-supersingular) affine point of the level-$N$ curve fixed by the square of Frobenius, integrality of $f$ at all places above $v$ forces both reductions to be regular, the first at $v$ and the second at the Frobenius translate of $v$. It is used in the construction of a prolongation tuple that is a model and satisfies the order law, [`ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed`](thm.html#ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_and_ord_residueSnd_nonneg_of_fixed_of_isAffineGeomPlace_of_notMem_ssPlaces_of_sp_eq_spPlace.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_SpecializationMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_nonneg_and_ord_residueSnd_nonneg_of_fixed_of_isAffineGeomPlace_of_notMem_ssPlaces_of_sp_eq_spPlace
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [DecidableEq k] (hqN : ¬ q ∣ N) (fm : CharPModel.FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hP : P.sp = fm.spPlace hred dataAll hsep)
    (R : ProlongationTuple P) :
    ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
        (v : Place k (modularFunctionFieldC k N)),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
        IsAffineGeomPlace k N v →
        v ∉ ssPlaces q N k →
        (∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
          P.reduceFst V = v → 0 ≤ V.ord f) →
        (R.residue₁ ⟨f, h₁⟩ ≠ 0 → 0 ≤ v.ord (R.residue₁ ⟨f, h₁⟩)) ∧
        (R.residue₂ ⟨f, h₂⟩ ≠ 0 →
          0 ≤ (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩)) := by sorry
