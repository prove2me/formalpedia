-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.cuspLawInfty_oneSided
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/34db948a-4326-5c86-8012-9eacc8475538
-- title:
--   One-sided first-copy cusp law at infinity-side cusps
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N \geq 1$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix also modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) together with the Kronecker congruence `hKr`, asserting that the bivariate reduction of $\Phi$ modulo $q$ factors as $(C(X)^q - X)(C(X) - X^q)$, and the integrality hypotheses `hα`, `hβ` on the two Hecke maps $\alpha$, $\beta$ from level $N$ to level $Nq$. Assume $q \nmid N$, and let $P$ be a place specialisation of level $N$ at $q$ over $(A, k, \mathrm{red})$, $R$ a prolongation tuple over $P$ satisfying `R.IsModel`, the conjunction of `R.DivisorLawFst`, `R.DivisorLawSnd`, `R.CuspLawInfty` and `R.CuspLawZero`. Then for every $f$ in the base-changed full modular function field $\overline{F}_{Nq}$ of level $Nq$ lying in the integers of the first regular prolongation `R.R₁`, whose first-copy residue `R.R₁.residue` is non-zero, for every divisor $D$ on $\overline{F}_{Nq}$ with $D(W) = \mathrm{ord}_W(f)$ at every place $W$, and for every place $c$ with `IsInftySide P c` (that is, $c$ is cuspidal in the sense of `IsCuspidal P` and $t_\infty(N,q)$ takes at $c$ a value $\tau \in A$ with $\mathrm{red}\,\tau = 1$), the push-forward along `P.reduceFst` of the restriction of $D$ to the infinity-side places, evaluated at `P.reduceFst c`, equals the order of `R.residue₁ ⟨f, h₁⟩` at `P.reduceFst c`. Here `P.reduceFst W` is obtained by restricting $W$ along the Hecke map $\bar\alpha$ and then applying the specialisation `P.sp`.
--
--   This is the first-copy half of the cusp-counting law on the bad fibre: the sum of the orders of $f$ over the infinity-side cusps of level $Nq$ lying above a cusp of the mod-$q$ curve of level $N$ matches the order of the reduced function there, in the style of the description of the fibres of $X_0(Np)$ at $p$ by Deligne and Rapoport. It is used by the corresponding zero-side statement `cuspLawZero_oneSided` and by the divisor bookkeeping for annulus data and for exhibiting functions with prescribed reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve
open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.cuspLawInfty_oneSided {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel) :
    ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers),
      R.R₁.residue ⟨f, h₁⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ W, D W = W.ord f) →
        ∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
          IsInftySide P c →
          Finsupp.mapDomain P.reduceFst (D.filter (IsInftySide P)) (P.reduceFst c)
            = (P.reduceFst c).ord (R.residue₁ ⟨f, h₁⟩) := by sorry
