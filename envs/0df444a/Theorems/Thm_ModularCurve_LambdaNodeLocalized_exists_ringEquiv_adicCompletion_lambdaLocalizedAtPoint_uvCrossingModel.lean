-- Prove2me | Theorems.Thm_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_adicCompletion_lambdaLocalizedAtPoint_uvCrossingModel
-- name    : ModularCurve.LambdaNodeLocalized.exists_ringEquiv_adicCompletion_lambdaLocalizedAtPoint_uvCrossingModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/6b85714d-c13f-5bd6-a7d9-7725aa9480ce
-- title:
--   Completed λ-node ring at a supersingular point is a crossing
-- statement:
--   Let $q$ be a prime with $q\ge 5$, let $A$ be a valuation subring of $\overline{\mathbb Q}$, let $k$ be a field of characteristic $q$ with decidable equality, and let $\mathrm{red}\colon A\to k$ be a ring homomorphism. Let $l\in k$ satisfy $l^{q^2}=l$, $l\neq 0$, $16l\neq 1$, and assume there is $a$ in `ssJSet q k` — the set of $j\in k$ such that every elliptic Weierstrass curve over $k$ with $j$-invariant $j$ has no nonzero affine point killed by $q$ — with $a\,(16l)^2(16l-1)^2=256\,((16l)^2-16l+1)^3$. Let $K\subset\overline{\mathbb Q}$ be an intermediate field finite over $\mathbb Q$, put $A_0:=$ `coeffSubring A K` $=A\cap K$ and let $\mathrm{red}_K:=$ `redRestrict red K` be $\mathrm{red}$ restricted to $A_0$. Assume given $y\in A_0$ with $\mathrm{red}_K(y)=l$; an element $\varpi\in A_0$ whose multiples are exactly the elements of $\ker\mathrm{red}_K$; an integer $e_K\ge 1$ and a unit $\varepsilon$ of $A_0$ with $q=\varpi^{e_K}\varepsilon$ in $A_0$. Write $S:=$ `lambdaLocalizedAtPoint q A₀ red_K l (l^q)`, the subring of Laurent series over $\overline{\mathbb Q}$ consisting of those $f$ for which there are $r,s\in A_0[X_0,X_1]$ with $s$ not vanishing at $(l,l^q)$ after applying $\mathrm{red}_K$ to coefficients and $f\cdot\Lambda(s)=\Lambda(r)$, where $\Lambda=$ `lambdaEval q A₀` is the evaluation sending $X_0\mapsto\lambda$ and $X_1\mapsto\lambda(q\,\cdot)$ and coefficients into Laurent series; $S$ is assumed Noetherian and local. Set $W:=A_0[[T]]/(T-\varpi)$ and let $\pi$ be the class of the constant series $\varpi$ in $W$. Then there exist a surjective ring homomorphism $\theta\colon W[[X_0,X_1]]\to \widehat S$ onto the $\mathfrak m_S$-adic completion of $S$, a unit $v$ of $\widehat S$, and a ring isomorphism $\iota\colon\widehat S\xrightarrow{\ \sim\ } W[[X_0,X_1]]/(X_0X_1-\pi^{e_K})$ such that: $\theta$ of the constant series with coefficient the class of $o\in A_0$ is the image in $\widehat S$ of $\Lambda(o)\in S$; $\iota(\theta(C\,o))=$ `UVCrossingModel.const` $(\pi^{e_K})\,o$ for every $o\in W$; $\iota$ of the image of $\Lambda(X_1-X_0^q)$ equals `UVCrossingModel.U` $(\pi^{e_K})\cdot\iota(v)$; and $\iota$ of the image of $\Lambda(X_0-X_1^q)$ equals `UVCrossingModel.V` $(\pi^{e_K})$.
--
--   This is the local structure theorem at a supersingular node of the level-two ($\lambda$, Legendre) model of the $q$-isogeny correspondence: the completed local ring is the regular crossing $UV=\varpi^{e_K}$ over $W=A_0[[T]]/(T-\varpi)$, in the form found in Katz–Mazur and Deligne–Rapoport. The isomorphism is branch-adapted, the two branch parameters being identified with $\lambda_q-\lambda^q$ (up to a unit) and $\lambda-\lambda_q^{\,q}$; it is used downstream to identify fixed points of the relevant group action on the crossing model and to express the wide-node model of $X_0(q)$ at exceptional $j$-invariants as a ring of invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_adicCompletion_lambdaLocalizedAtPoint_uvCrossingModel.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open ModularCurve.NodeLocalized
open IsLocalRing
open ModularCurve
open ModularCurve.LambdaNodeLocalized

theorem ModularCurve.LambdaNodeLocalized.exists_ringEquiv_adicCompletion_lambdaLocalizedAtPoint_uvCrossingModel
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (l : k) (hl2 : l ^ (q ^ 2) = l) (hl0 : l ≠ 0) (hl1 : 16 * l ≠ 1)
    (hss : ∃ a ∈ ssJSet q k, a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (y : ↥(coeffSubring A K)) (hy : redRestrict red K y = l)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (heK : 1 ≤ eK) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε)
    [IsNoetherianRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))]
    [IsLocalRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))] :
    ∃ (θ : MvPowerSeries (Fin 2) (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) →+* AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
      (v : (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))ˣ)
      (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≃+*
        UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) ^ eK)),
      Function.Surjective θ ∧
      (∀ o : ↥(coeffSubring A K), θ (MvPowerSeries.C (Ideal.Quotient.mk _ (PowerSeries.C o))) = algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) _
          (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C o),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))) ∧
      (∀ o : (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}), ι (θ (MvPowerSeries.C o)) = UVCrossingModel.const ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) ^ eK) o) ∧
      ι (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) _
          (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))) =
        UVCrossingModel.U ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) ^ eK) * ι (v : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ∧
      ι (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) _
          (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))) =
        UVCrossingModel.V ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) ^ eK) := by sorry
