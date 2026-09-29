-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_of_reduceFst_fixed_ordinary_of_regularityLaw
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_commonUnit_pole_of_reduceFst_fixed_ordinary_of_regularityLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/0d77e14f-afaf-535f-9c4e-69caed67653e
-- title:
--   Common unit with a simple pole above an ordinary fixed place
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N \ge 1$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Let `data` be modular polynomial data for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions) satisfying the Kronecker congruence `hKr`, namely that $\Phi$ reduced modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$; let `hα`, `hβ` assert integrality of the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of the level-$N$ into the level-$Nq$ geometric function field over $\overline{\mathbb{Q}}$. Let $P$ be a place specialisation, sending places of `modularFunctionFieldBar N` to places of `modularFunctionFieldC k N` compatibly with the orders of $j$ and $j_N$, and let $R$ be a prolongation tuple for $P$, consisting of two regular prolongations $R_1, R_2$ of $A$ to the level-$Nq$ field with residue fields in `modularFunctionFieldFullC (ResidueField A) N`, matched by the Atkin–Lehner involution and compatible with coefficientwise reduction. Assume $R$ is a model (the two divisor laws for places not fixed by the square of geometric Frobenius, together with the cusp laws at the infinity and zero sides), that $R$ satisfies the fixed-place order law `hO`, that $W$ is precisely the finite set `ssPlaces q N k` of supersingular places and that $R$ satisfies `RegularityLaw W`, and that $q \nmid N$. Let $V_0$ be a place of the level-$Nq$ field whose first reduction $v = P.\mathrm{reduceFst}\, V_0$ is fixed by the square of `frobOnPlacesGeomLevel`, is affine (both generators $j$, $j_N$ of the level-$N$ geometric field lie in its valuation subring) and is not supersingular; let $S \subseteq k$ and $B$ a finite set of places of `modularFunctionFieldC k N` be arbitrary finite sets. Then there is $g$ in the level-$Nq$ field, lying in the integers of both $R_1$ and $R_2$, with both residues $R_1$-residue and $R_2$-residue of $g$ nonzero, with $\mathrm{ord}_{V_0}(g) = -1$, such that every other pole $V \neq V_0$ of $g$ satisfies: $j - a$ has positive order at $V$ for some $a \in A$ with $\mathrm{red}\,a \notin S$, and both $P.\mathrm{reduceFst}\,V$ and $P.\mathrm{reduceSnd}\,V$ avoid $B$; and, for the images `R.residue₁`, `R.residue₂` of the two residues in `modularFunctionFieldC k N`, either $\mathrm{ord}_v(R.\mathrm{residue}_1 g) = -1$ and $\mathrm{ord}_{\mathrm{Frob}(v)}(R.\mathrm{residue}_2 g) = 0$, or $\mathrm{ord}_v(R.\mathrm{residue}_1 g) = 0$ and $\mathrm{ord}_{\mathrm{Frob}(v)}(R.\mathrm{residue}_2 g) = -1$.
--
--   This is the approximation step in the analysis of the two-component special fibre of $X_0(Nq)$ at $q$: it produces a function with a prescribed simple pole above an ordinary point fixed by the square of Frobenius, whose remaining poles are in general position relative to prescribed finite sets, and whose pole lies on exactly one of the two components. It feeds the residue-field version of the same statement and the construction of representatives of divisor classes used in the specialisation of Picard groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_of_reduceFst_fixed_ordinary_of_regularityLaw.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_commonUnit_pole_of_reduceFst_fixed_ordinary_of_regularityLaw
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]
    (k : Type) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
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
