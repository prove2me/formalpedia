-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_of_reduceFst_fixed_ordinary_of_regularityLaw_univ
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_commonUnit_pole_of_reduceFst_fixed_ordinary_of_regularityLaw_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/14a6fd14-6230-5760-857e-dc8cdb4e172a
-- title:
--   Common unit with simple pole over an ordinary fixed place
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb{Q}}$, $N \ge 1$, and $k$ an algebraically closed field of characteristic $q$ equipped with a ring homomorphism $\mathrm{red} \colon A \to k$; let $data$ be modular polynomial data for $q$ (a monic bivariate $\Phi$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) satisfying the Kronecker congruence $\Phi \equiv (Y^q - X)(Y - X^q)$ modulo $q$, and assume the two degeneracy maps $\overline{\mathbb{Q}}$-embedding the level-$N$ into the level-$Nq$ modular function field are integral (hypotheses $h\alpha$, $h\beta$). Let $P$ be a place specialisation of these data and $R$ a prolongation tuple over $P$, consisting of two regular prolongations $R_1, R_2$ of $A$ to the level-$Nq$ field with residue fields inside the level-$N$ function field over the residue field of $A$, together with the compatibilities of the tuple. Assume $R$ satisfies `IsModel` (the two divisor laws on the non-fixed places and the two cusp laws) and `OrderLawFixed` (for a common unit $f$, the pushforward along `reduceFst` of the divisor of $f$ at a Frobenius-square-fixed affine place $v$ equals $\operatorname{ord}_v \bar f_1 + \operatorname{ord}_{\varphi v} \bar f_2$, where $\varphi$ is `frobOnPlacesGeomLevel`). Let $W$ be a finite set of places of the level-$N$ field over $k$ with $R$ satisfying `RegularityLaw W`, and suppose $W$ is exactly the set of supersingular places (rational, affine, with $j$-value supersingular) and $q \nmid N$. Let $V_0$ be a place of the level-$Nq$ field over $\overline{\mathbb{Q}}$ whose first reduction $v = P.\mathrm{reduceFst}(V_0)$ satisfies $\varphi(\varphi(v)) = v$, is affine (both $j$ and $j_N$ lie in its valuation subring) and is not supersingular. Then for every finite $S \subseteq k$ and every finite set $B$ of places of the level-$N$ field over $k$ there exists $g$ in the level-$Nq$ field, integral for both $R_1$ and $R_2$, with both residues $\bar g_1, \bar g_2$ non-zero, such that $\operatorname{ord}_{V_0} g = -1$; every other pole $V \neq V_0$ of $g$ satisfies $\operatorname{ord}_V(j - a) > 0$ for some $a \in A$ with $\mathrm{red}(a) \notin S$, and both $P.\mathrm{reduceFst}(V)$ and $P.\mathrm{reduceSnd}(V)$ avoid $B$; and either $\operatorname{ord}_v \bar g_1 = -1$ with $\operatorname{ord}_{\varphi v} \bar g_2 = 0$, or $\operatorname{ord}_v \bar g_1 = 0$ with $\operatorname{ord}_{\varphi v} \bar g_2 = -1$.
--
--   This is the existence statement for a test function on $X_0(Nq)$ with a single prescribed simple pole above an ordinary point of the special fibre at $q$, whose pole survives on exactly one of the two components of the reduction, with all remaining poles pushed into general position away from prescribed finite sets of $j$-values and of places. It is used to establish the branchwise divisor law on the ordinary sheets, specifically in [`ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_of_regularityLaw`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_of_regularityLaw).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_of_reduceFst_fixed_ordinary_of_regularityLaw_univ.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false
open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization.ProlongationTuple
open ModularCurve.PlaceSpecialization hiding jFun

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_commonUnit_pole_of_reduceFst_fixed_ordinary_of_regularityLaw_univ
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hRL : R.RegularityLaw W)
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k) (hqN : ¬ q ∣ N)
    (V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V₀))
      = P.reduceFst V₀)
    (haff : IsAffineGeomPlace k N (P.reduceFst V₀)) (hord : P.reduceFst V₀ ∉ ssPlaces q N k)
    (S : Finset k) (B : Finset (Place k (modularFunctionFieldC k N))) :
    ∃ (g : modularFunctionFieldBar (N * q)) (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers),
      R.R₁.residue ⟨g, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨g, h₂⟩ ≠ 0 ∧ V₀.ord g = -1 ∧
      (∀ V, V ≠ V₀ → V.ord g < 0 →
        (∃ a : A, 0 < V.ord (jFun N q - algebraMap (AlgebraicClosure ℚ)
            (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) ∧ red a ∉ S) ∧
          P.reduceFst V ∉ B ∧ P.reduceSnd V ∉ B) ∧
      (((P.reduceFst V₀).ord (R.residue₁ ⟨g, h₁⟩) = -1 ∧
          (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V₀)).ord (R.residue₂ ⟨g, h₂⟩) = 0) ∨
        ((P.reduceFst V₀).ord (R.residue₁ ⟨g, h₁⟩) = 0 ∧
          (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V₀)).ord (R.residue₂ ⟨g, h₂⟩) = -1)) := by sorry
