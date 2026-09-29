-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_divisor_oneSidedFst_laws_modularUnit
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_divisor_oneSidedFst_laws_modularUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/3ec863d0-9f39-50f0-8e2e-240844772731
-- title:
--   One-sided divisor laws for the modular unit Δ/Δ_q
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive level $N$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$, together with modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][X']$ of degree $\psi(q)$ killing the pair $(j, j_q)$ of $q$-expansions) satisfying the Kronecker congruence $\Phi \equiv (X'^q - X)(X' - X^q) \bmod q$, and hypotheses $h\alpha$, $h\beta$ asserting that the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of the level-$N$ into the level-$Nq$ function field over $\overline{\mathbb{Q}}$ are integral ring maps. Assume $q \nmid N$, let $P$ be a place specialisation of the level-$N$ curve attached to these data, and let $R$ be a prolongation tuple over $P$ which is a model, i.e. satisfies the two divisor laws and the two cusp laws. Let $u$ be an element of the level-$Nq$ function field `modularFunctionFieldBar (N * q)` whose underlying Laurent series is the image under coefficientwise base change of the level-$q$ modular unit `modularUnitSeries q` $= \Delta/\Delta_q$, and assume $u$ lies in the first-side valuation subring `R.R₁.integers`. Then there is a finitely supported divisor $D$ on the places of the level-$Nq$ function field such that: $D(W) = \mathrm{ord}_W(u)$ for every place $W$; for every place $v$ of `modularFunctionFieldC k N` not fixed by the square of `frobOnPlacesGeomLevel`, the push-forward along $W \mapsto P.\mathrm{reduceFst}\,W$ (reduction through `heckeAlphaBar` followed by $P.\mathrm{sp}$) of the restriction of $D$ to the places $W$ with $\mathrm{Frob}(P.\mathrm{reduceFst}\,W) = P.\mathrm{reduceSnd}\,W$ and $\mathrm{Frob}^2(P.\mathrm{reduceFst}\,W) \neq P.\mathrm{reduceFst}\,W$ takes at $v$ the value $\mathrm{ord}_v$ of the first residue $R.\mathrm{residue}_1(u)$; and for every place $c$ on the $\infty$-side (cuspidal, with $\mathrm{ord}_c(j_{N,q} - a) \le 0$ for all $a \in A$, and $t_\infty = j_{Q}/j^{q}$ taking at $c$ a value $\tau \in A$ with $\mathrm{red}\,\tau = 1$), the push-forward along $P.\mathrm{reduceFst}$ of the $\infty$-side part of $D$ takes at $P.\mathrm{reduceFst}\,c$ the value $\mathrm{ord}_{P.\mathrm{reduceFst}\,c}(R.\mathrm{residue}_1(u))$. Unlike the general divisor and cusp laws, only membership of $u$ in the first-side integers is assumed, with no second-side hypothesis and no non-vanishing of residues.
--
--   The underlying classical input is the computation of the divisor of the modular unit $\Delta/\Delta_q$, supported at the two cusps of $X_0(q)$, whose reduction modulo $q$ reads off the supersingular places. This one-sided statement is used to establish the unconditional first- and second-side divisor laws and the $\infty$-cusp law for prolongation tuples, `divisorLawFst_oneSided`, `divisorLawSnd_oneSided` and `cuspLawInfty_oneSided`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_divisor_oneSidedFst_laws_modularUnit.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve ModularCurve
open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_divisor_oneSidedFst_laws_modularUnit
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (h₁ : u ∈ R.R₁.integers) :
    ∃ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord u) ∧
      (∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
        Finsupp.mapDomain P.reduceFst (D.filter P.IsStrictFst) v
          = v.ord (R.residue₁ ⟨u, h₁⟩)) ∧
      (∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        IsInftySide P c →
        Finsupp.mapDomain P.reduceFst (D.filter (IsInftySide P)) (P.reduceFst c)
          = (P.reduceFst c).ord (R.residue₁ ⟨u, h₁⟩)) := by sorry
