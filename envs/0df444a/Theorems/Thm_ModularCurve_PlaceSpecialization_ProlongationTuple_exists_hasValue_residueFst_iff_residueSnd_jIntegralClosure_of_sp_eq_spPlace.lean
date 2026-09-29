-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/b68c5c6b-df44-52af-8274-7bec6fc0daa2
-- title:
--   Agreement of the two residue conditions at a supersingular node
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive integer $N$, an algebraically closed field $k$ of characteristic $q$ and a surjective ring homomorphism $\mathrm{red} : A \to k$; assume $q \nmid N$. Further data: modular polynomial data `data` for $q$ satisfying the Kronecker congruence $\Phi \equiv (X'^{q}-X)(X'-X^{q}) \bmod q$; integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings of the level-$N$ into the level-$Nq$ function field over $\overline{\mathbb{Q}}$; a fibre model `fm` of level $N$ over $A$ reducing to $k$; modular polynomial data `dataAll` for every divisor of $N$, with the separability hypothesis `hsep` on the image of $\Phi_N$ over $\mathrm{RatFunc}\,k$; a place specialisation $P$ whose place map `P.sp` equals `fm.spPlace hred dataAll hsep`; a prolongation tuple $R$ over $P$, providing two regular prolongations $R_1, R_2$ of $A$ to the level-$Nq$ function field with residue maps `R.residue₁`, `R.residue₂` into the level-$N$ fibre field $\mathrm{modularFunctionFieldC}\,k\,N$; and a place $w$ of that field lying in `ssPlaces q N k`, i.e. $w$ is rational, is an affine geometric place, and its value at `jGeomGen k N` lies in `ssJSet q k`. The conclusion is an eventual statement in the base field: for every intermediate field $K$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ of finite degree there is a finite extension $K' \supseteq K$ inside $\overline{\mathbb{Q}}$ such that for every finite $K'' \supseteq K'$ and every $t$ in the level-$Nq$ function field over $\overline{\mathbb{Q}}$ whose Laurent series lies in $\mathrm{jIntegralClosure}\,(Nq)\,A\,K''$ (elements of `fieldOver (N*q) K''` integral over `jRing A K''`): first, $t$ lies in the valuation ring of $R_1$ with `R.residue₁ t` having value $0$ at $w$ if and only if $t$ lies in the valuation ring of $R_2$ with `R.residue₂ t` having value $0$ at the translate $\mathrm{arithFrobC}\,q\,k\,N \cdot w$ (translation by the coefficientwise $q$-power Frobenius); and second, $t$ lies in the valuation ring of $R_1$ and `R.residue₁ t` has at $w$ a value of the form $\mathrm{red}(c)$ for some $c \in A \cap K''$.
--
--   This is the algebraic description of the node of the level-$Nq$ fibre at $q$ above a supersingular point of the level-$N$ fibre: the vanishing condition read off from the first branch at $w$ matches the one read off from the second branch at the Frobenius translate of $w$, and the common residue value is realised by a constant from $A \cap K''$, once the base field is enlarged enough. It feeds the two subsequent statements comparing values of the two residue maps and producing constants for residues of integral elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_SpecializationMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (fm : CharPModel.FibreModel N A q k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hP : P.sp = fm.spPlace hred dataAll hsep)
    (R : ProlongationTuple P)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) :
    ∀ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K →
      ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K'), K ≤ K' ∧
        ∀ (K'' : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ K'' → K' ≤ K'' →
          (∀ (t : ↥(modularFunctionFieldBar (N * q))),
              (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K'' →
              ((∃ h₁ : t ∈ R.R₁.integers, w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k)) ↔
                (∃ h₂ : t ∈ R.R₂.integers,
                  (arithFrobC q k N • w).HasValue (R.residue₂ ⟨t, h₂⟩ : ↥(modularFunctionFieldC k N)) (0 : k)))) ∧
          (∀ (t : ↥(modularFunctionFieldBar (N * q))),
              (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K'' →
              ∃ (c : ↥(coeffSubring A K'')) (h₁ : t ∈ R.R₁.integers),
                w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (redRestrict red K'' c)) := by sorry
