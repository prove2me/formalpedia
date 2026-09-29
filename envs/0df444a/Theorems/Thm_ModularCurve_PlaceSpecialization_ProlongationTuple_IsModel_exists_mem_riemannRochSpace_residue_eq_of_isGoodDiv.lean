-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mem_riemannRochSpace_residue_eq_of_isGoodDiv
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_mem_riemannRochSpace_residue_eq_of_isGoodDiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/09a55518-47a8-51e9-ae44-3795d4cc3648
-- title:
--   Realising a node-compatible residue pair by a bi-integral section
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a nonzero $N$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, integrality hypotheses `hα`, `hβ` for the two level-raising maps $\overline{\mathcal F}(N) \to \overline{\mathcal F}(Nq)$, and a place specialisation $P$ for these data. Assume $q \nmid N$, let $W$ be a finite set of places of `modularFunctionFieldC k N` whose members are exactly the supersingular places `ssPlaces q N k`, and let $R$ be a prolongation tuple over $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), the regularity law and the node-value law at $W$, and the fixed-order law. Let $D$ be an effective divisor of $\overline{\mathcal F}(Nq)$ over $\overline{\mathbb{Q}}$ such that every place in the support of $D$ is `IsStrictFst` or `IsStrictSnd`, and suppose that the push-forward along `P.reduceFst` of the strict-first part of $D$ has degree at least $2g_0 - 1 + \#W$ and the push-forward along `P.reduceSnd` of the strict-second part has degree at least $2g_0 - 1$, where $g_0 =$ `genusFF k (modularFunctionFieldC k N)`. Let $g_1, g_2$ be elements of `modularFunctionFieldFullC (ResidueField A) N` whose images under $R.\iota$ lie in the Riemann–Roch spaces of these two pushed-forward divisors, and assume that for every pair $s$ in `nodePairsOfPlaces (arithFrobC q k N) W` there is a $c \in k$ such that $\iota g_1$ has value $c$ at $s.1$ and $\iota g_2$ has value $c$ at $s.2$ (that is, each lies in the respective valuation subring and reduces to the image of $c$). Then there exists $G$ in `modularFunctionFieldBar (N * q)` lying in the valuation subrings `R.R₁.integers` and `R.R₂.integers`, belonging to the Riemann–Roch space of $D$, and with $R.R_1$-residue $g_1$ and $R.R_2$-residue $g_2$.
--
--   This is the surjectivity half of the dictionary between sections of $\mathcal O(D)$ on the level-$Nq$ curve that are integral for both prolongations and pairs of functions on the two components of the special fibre agreeing at the supersingular nodes: any node-compatible pair in the prescribed Riemann–Roch spaces is realised as a residue pair. It is used to produce a bi-integral function whose divisor has prescribed simple behaviour at places of strict type, in [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mem_riemannRochSpace_residue_eq_of_isGoodDiv.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open ModularCurve
open AlgebraicCurve

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_mem_riemannRochSpace_residue_eq_of_isGoodDiv
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : 0 ≤ D) (hgood : P.IsGoodDiv D)
    (hdeg₁ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 + W.card ≤
      (Finsupp.mapDomain P.reduceFst (P.fstDiv D)).degree)
    (hdeg₂ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 ≤
      (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)).degree)
    (g₁ g₂ : ↥(modularFunctionFieldFullC (ResidueField A) N))
    (hg₁ : (R.ι g₁ : ↥(modularFunctionFieldC k N)) ∈
      riemannRochSpace (Finsupp.mapDomain P.reduceFst (P.fstDiv D)))
    (hg₂ : (R.ι g₂ : ↥(modularFunctionFieldC k N)) ∈
      riemannRochSpace (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)))
    (hnode : ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W, ∃ c : k,
      s.1.HasValue (R.ι g₁ : ↥(modularFunctionFieldC k N)) c ∧
      s.2.HasValue (R.ι g₂ : ↥(modularFunctionFieldC k N)) c) :
    ∃ (G : ↥(modularFunctionFieldBar (N * q))) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers),
      G ∈ riemannRochSpace D ∧ R.R₁.residue ⟨G, h₁⟩ = g₁ ∧ R.R₂.residue ⟨G, h₂⟩ = g₂ := by sorry
