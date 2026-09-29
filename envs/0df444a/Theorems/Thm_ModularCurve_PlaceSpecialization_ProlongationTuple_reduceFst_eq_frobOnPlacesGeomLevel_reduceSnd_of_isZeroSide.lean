-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/305aa1cf-e0cc-52e0-8977-7a7f1ede705b
-- title:
--   The 0-side Frobenius relation between the two reductions
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an integer $N\ge 1$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Let `data` consist of a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the relevant $q$-expansion, and let `hKr` be the Kronecker congruence that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$; let `hα`, `hβ` assert that the two Hecke maps $\bar\alpha,\bar\beta$ from level $N$ to level $Nq$ are integral ring homomorphisms. Let $P$ be a place specialization of these data — in particular a map `P.sp` from places of the level-$N$ function field over $\overline{\mathbb{Q}}$ to places of the characteristic-$q$ level-$N$ function field over $k$, together with its compatibility clauses — and assume $q \nmid N$. Then for every place $c$ of the level-$Nq$ function field over $\overline{\mathbb{Q}}$ which is on the $0$-side, i.e. is cuspidal in the sense of `IsCuspidal'` and has $t_0(N,q)$ in its valuation ring with residue the image of some $\tau \in A$ with $red\,\tau = 1$, one has $P.\mathrm{reduceFst}\,c = \mathrm{frob}(P.\mathrm{reduceSnd}\,c)$; here $\mathrm{reduceFst}\,c$ (resp. $\mathrm{reduceSnd}\,c$) is `P.sp` applied to the restriction of $c$ along $\bar\alpha$ (resp. $\bar\beta$), and $\mathrm{frob}$ is `frobOnPlacesGeomLevel`, the transport of a place along the geometric Frobenius isomorphism of the level-$N$ function field in characteristic $q$ after restriction to its Frobenius image.
--
--   This is the $0$-side half of the Eichler–Shimura style dichotomy attached to the Kronecker congruence: on the two components of the reduction of the level-$Nq$ modular curve, the two degeneracy reductions of a place differ by geometric Frobenius, in one order on the $\infty$-side and in the other on the $0$-side. It feeds the cusp law and the regularity-law arguments producing common units with prescribed poles at the first and second reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N) :
    ∀ c, IsZeroSide P c → P.reduceFst c = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd c) := by sorry
