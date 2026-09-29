-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_iff_hasValue_residueFst_zero_jIntegralClosure_of_sp_eq_spPlace
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_hasValue_iff_hasValue_residueFst_zero_jIntegralClosure_of_sp_eq_spPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/08fc17cd-8007-5c63-8027-59d9fd999cf4
-- title:
--   Node value law at a supersingular place of level Nq
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an integer $N\neq 0$ with $q\nmid N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A\to k$ which is surjective. Fix moreover: `data`, a monic $\Phi\in\mathbb{Z}[X][Y]$ of degree $\psi(q)$ with $\Phi(j,j_q)=0$, together with `hKr`, the Kronecker congruence $\Phi\bmod q=(X^q-Y)(X-Y^q)$ in the bivariate reduction; `hα`, `hβ`, integrality of the two degeneracy maps $\bar\alpha,\bar\beta$ from level $N$ to level $Nq$; `fm`, a fibre model of level $N$ over $A$ at $q$ with reduction $\mathrm{red}$, i.e. subrings $B_{\mathrm{fin}},B_{\infty}$ of the level-$N$ Laurent-series field over $\overline{\mathbb{Q}}$ containing the constants from $A$ and $j,j_N$ respectively $j^{-1}$, integral over the affine bases, with reduction homomorphisms $\pi_{\mathrm{fin}},\pi_{\infty}$ to $\mathrm{modularFunctionFieldC}\ k\ N$ compatible with constants and with $j$; a family `dataAll` of such modular polynomial data for all divisors of $N$, and `hsep`, separability of the image of $\Phi_N$ over $\mathrm{RatFunc}\ k$; a place specialisation $P$ for these data whose map on places satisfies $P.\mathrm{sp}=fm.\mathrm{spPlace}$; a prolongation tuple $R$ over $P$, providing in particular the regular prolongation $R_1$ with residue map $\mathrm{residue}_1$; and a place $w$ of $\mathrm{modularFunctionFieldC}\ k\ N$ lying in $\mathrm{ssPlaces}\ q\ N\ k$, that is, a supersingular place. The conclusion is an eventual statement in the base field: for every $K\subseteq\overline{\mathbb{Q}}$ finite over $\mathbb{Q}$ there is a finite extension $K'\supseteq K$ inside $\overline{\mathbb{Q}}$ such that for every finite $K''$ with $K'\le K''$, every place $V$ of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb{Q}}$ with $P.\mathrm{reduceFst}\,V=w$ (the specialisation of the restriction of $V$ along $\bar\alpha$ is $w$), and every $t$ in $\mathrm{modularFunctionFieldBar}(Nq)$ whose underlying Laurent series lies in $\mathrm{jIntegralClosure}(Nq)\,A\,K''$ (elements of $\mathrm{fieldOver}(Nq)\,K''$ integral over $\mathrm{jRing}\,A\,K''$), there exists $a\in A$ with $V$ taking the value $a$ at $t$ ($t$ lies in the valuation subring of $V$ and its residue is the image of $a$), and such that $a$ lies in the maximal ideal of $A$ if and only if $t$ lies in the integers of $R_1$ and $w$ takes the value $0$ at $\mathrm{residue}_1(t)$.
--
--   This is the value half of the identification of the ideal of a node on the special fibre of $X_0(Nq)$ at $q$: it says that, after enlarging the base number field, the reduction of a function of the level-$Nq$ normalisation at a place above a supersingular point is governed by the vanishing of its first-component residue at that point. It is the one step where the hypothesis that $P.\mathrm{sp}$ comes from the fibre model is used, and it feeds the companion statement on values of residues and the description of the completed local rings at the supersingular nodes as crossing models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_iff_hasValue_residueFst_zero_jIntegralClosure_of_sp_eq_spPlace.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_hasValue_iff_hasValue_residueFst_zero_jIntegralClosure_of_sp_eq_spPlace
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
          ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
            ∀ (t : ↥(modularFunctionFieldBar (N * q))),
              (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K'' →
              ∃ a : A, V.HasValue t (a : AlgebraicClosure ℚ) ∧
                ((∃ h₁ : t ∈ R.R₁.integers, w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k)) ↔
                  a ∈ IsLocalRing.maximalIdeal A) := by sorry
