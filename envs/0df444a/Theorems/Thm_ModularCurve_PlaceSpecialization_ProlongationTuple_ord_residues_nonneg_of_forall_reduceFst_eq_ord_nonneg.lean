-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residues_nonneg_of_forall_reduceFst_eq_ord_nonneg
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residues_nonneg_of_forall_reduceFst_eq_ord_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/2e829fc3-1503-5d4a-9395-45e32ef75f3f
-- title:
--   Regularity of both residues at a φ²-fixed affine place
-- statement:
--   Fix $N\ge 1$ and a prime $q$ with $q\nmid N$, a valuation subring $A$ of $\overline{\mathbb Q}$, and an algebraically closed field $k$ of characteristic $q$ with decidable equality, together with a ring homomorphism $\mathrm{red}\colon A\to k$; assume every nonzero element of the level-$Nq$ function field $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb Q}$ has a principal divisor of degree $0$ (the class `HasPrincipalDivisors`). Let `data` be a `ModularPolynomialData q`, i.e. a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ vanishing on $(j(q),j(q^{\,\cdot}))$, satisfying the Kronecker congruence $\Phi\equiv (X^q-Y)(X-Y^q)$ mod $q$, and let $h\alpha,h\beta$ assert integrality of the two Hecke maps $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ at level $(N,q)$ over $\overline{\mathbb Q}$. Let $P$ be a `PlaceSpecialization` for these data and $R$ a `ProlongationTuple` over $P$ satisfying `R.IsModel` (the two divisor laws and the two cusp laws) and `R.OrderLawFixed` (at every $\varphi^2$-fixed affine place the pushforward along $P.\mathrm{reduceFst}$ of a divisor of a function equals the sum of the orders of its two residues at $v$ and $\varphi v$). Let $f$ lie in the integers of both prolongations $R.R_1$, $R.R_2$, let $v$ be a place of $\mathrm{modularFunctionFieldC}\ k\ N$ with $\varphi(\varphi v)=v$ for $\varphi=\mathrm{frobOnPlacesGeomLevel}$, and affine in the sense that both $j$- and $j_N$-generators lie in its valuation subring. Assuming $V.\mathrm{ord}\,f\ge 0$ for every place $V$ of the level-$Nq$ field with $P.\mathrm{reduceFst}\,V=v$, the conclusion is the conjunction: if $R.\mathrm{residue}_1 f\ne 0$ then $v.\mathrm{ord}(R.\mathrm{residue}_1 f)\ge 0$, and if $R.\mathrm{residue}_2 f\ne 0$ then $(\varphi v).\mathrm{ord}(R.\mathrm{residue}_2 f)\ge 0$.
--
--   This is the level-$N$ form, for $q\nmid N$, of the first clause of the regularity law for reduction of the modular curve $X_0(Nq)$ in characteristic $q$: absence of poles upstairs in the fibre of $\mathrm{reduceFst}$ over a $\varphi^2$-fixed affine place forces both residues to be regular, on their respective sheets. It feeds the construction of common units with prescribed poles and the vanishing statements for orders of the first residue.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residues_nonneg_of_forall_reduceFst_eq_ord_nonneg.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residues_nonneg_of_forall_reduceFst_eq_ord_nonneg
    {N : ℕ} [NeZero N] {q : ℕ} [Fact q.Prime] (hqN : ¬ q ∣ N)
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] [DecidableEq k] [IsAlgClosed k]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))]
    {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (v : Place k (modularFunctionFieldC k N))
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v)
    (haff : IsAffineGeomPlace k N v)
    (hpole : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.reduceFst V = v → 0 ≤ V.ord f) :
    (R.residue₁ ⟨f, h₁⟩ ≠ 0 → 0 ≤ v.ord (R.residue₁ ⟨f, h₁⟩)) ∧
    (R.residue₂ ⟨f, h₂⟩ ≠ 0 → 0 ≤ (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩)) := by sorry
