-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_sum_height_mul_multidegree_comp_eq_depthDiv_and_apply_inl_one_eq_degree_sndDiv_level
-- name    : ModularCurve.PlaceSpecialization.sum_height_mul_multidegree_comp_eq_depthDiv_and_apply_inl_one_eq_degree_sndDiv_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/6333131c-18d4-520a-999c-780b3e4b7992
-- title:
--   Depth dictionary gives the depth divisor and second-branch degree
-- statement:
--   Fix a prime $q$ and $N\ge 1$, a valuation subring $A$ of $\overline{\mathbf Q}$, an algebraically closed perfect field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, modular polynomial data `data` at $q$ satisfying the Kronecker congruence (the reduction mod $q$ of $\Phi$ equals $(\mathrm{C}\,X^q-X)(\mathrm{C}\,X-X^q)$), integrality of the two degeneracy embeddings from level $N$ to level $Nq$ over $\overline{\mathbf Q}$, and a `PlaceSpecialization` $P$ for these data. Further data: a finite set $W$ of places of $k(X_0(N)) =$ `modularFunctionFieldC k N`, a width function $e$ on such places, a depth function on the places of `modularFunctionFieldBar (N*q)`, and a degree-zero divisor $D_0$ on the latter. It is assumed that every place $V'$ of $\operatorname{supp} D_0$ satisfies exactly one of: $P$ is strict of the first kind at $V'$ (i.e. the geometric-level Frobenius carries $P.\mathrm{reduceFst}\,V'$ to $P.\mathrm{reduceSnd}\,V'$, while its square moves $P.\mathrm{reduceFst}\,V'$), strict of the second kind at $V'$ (the symmetric condition), or $P.\mathrm{reduceFst}\,V' \in W$ with $0 < \mathrm{depth}\,V' < e(P.\mathrm{reduceFst}\,V')$; moreover the two strictness conditions never hold simultaneously, and neither holds when $P.\mathrm{reduceFst}\,V' \in W$. A finite type `node` with widths `wd` is identified with $W$ by $\sigma_N$ so that $\mathrm{wd}(\sigma_N w) = e(w)$. The support of $D_0$ is enumerated by a bijection $\mathrm{idx} : \mathrm{Fin}\,m \simeq \operatorname{supp} D_0$, with natural numbers $\mathrm{pos}_j,\mathrm{neg}_j$ such that $\mathrm{pos}_j-\mathrm{neg}_j = D_0(\mathrm{idx}\,j)$, and components $v_j$ of $\mathrm{Fin}\,2 \oplus \coprod_{n}\mathrm{Fin}(\mathrm{wd}\,n-1)$ assigned by the dictionary governed by an orientation bit `swap`: the two branches $\mathrm{inl}\,0,\mathrm{inl}\,1$ (interchanged when `swap` is true) for the places strict of the first and second kind respectively, and otherwise `DRResolvedModelPackage.chainPos wd` at $\sigma_N$ of the reduction, at chain position $\mathrm{depth}(\mathrm{idx}\,j)$, or $\mathrm{wd}(\sigma_N\cdot) - \mathrm{depth}(\mathrm{idx}\,j)$ when `swap` is true (places outside these cases receive $\mathrm{inl}\,0$). Finally $\Phi$ is any bijection from the component set indexed by the node pairs $\{(w, \mathrm{Frob}\cdot w) : w \in W\}$ with widths $s \mapsto e(s_1)$ onto the one indexed by `node`, which carries $\mathrm{inl}\,0,\mathrm{inl}\,1$ to themselves or swaps them according to `swap`, and which on each chain is the index-preserving map if `swap` is false and the order-reversing map ($kk + kk' + 2 = \mathrm{wd}$) if `swap` is true. The conclusion is the conjunction of: for every node pair $s$, $\sum_{kk < e(s_1)-1} (kk+1)\sum_{j : v_j = \Phi(\mathrm{inr}\langle s,kk\rangle)} (\mathrm{pos}_j-\mathrm{neg}_j) = (P.\mathrm{depthDiv}\,\mathrm{depth}\,D_0)(s_1)$, where $P.\mathrm{depthDiv}$ pushes each $V'$ forward to $P.\mathrm{reduceFst}\,V'$ with multiplicity $D_0(V')\cdot \mathrm{depth}\,V'$; and $\sum_{j : v_j = \Phi(\mathrm{inl}\,1)} (\mathrm{pos}_j-\mathrm{neg}_j)$ equals the degree of $P.\mathrm{sndDiv}\,D_0$, the restriction of $D_0$ to the places at which $P$ is strict of the second kind.
--
--   This is the bookkeeping step that translates the depth dictionary on places of $X_0(Nq)_{\overline{\mathbf Q}}$ into multidegree data on the components of the resolved Deligne–Rapoport model over $k$: chain heights weighted by multiplicities recover the depth divisor at each glued pair, and the second branch records the degree of the strict-second-kind part of the divisor. It is used in the proof of [`ModularCurve.DRModelPackageLevel.comp_eq_zero_of_exists_schemeHomOver_of_depthCompLaw_of_abelJacobiPin_of_surjective_red_of_sp_eq_spPlace`](thm.html#ModularCurve.DRModelPackageLevel.comp_eq_zero_of_exists_schemeHomOver_of_depthCompLaw_of_abelJacobiPin_of_surjective_red_of_sp_eq_spPlace); that the degree of a divisor on `modularFunctionFieldBar (N*q)` is the plain sum of its multiplicities comes from [`ModularCurve.deg_eq_one_modularFunctionFieldBar`](thm.html#ModularCurve.deg_eq_one_modularFunctionFieldBar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_sum_height_mul_multidegree_comp_eq_depthDiv_and_apply_inl_one_eq_degree_sndDiv_level.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization MazurRapoportAppendix
open scoped BigOperators

set_option maxHeartbeats 400000 in
open Classical in

theorem ModularCurve.PlaceSpecialization.sum_height_mul_multidegree_comp_eq_depthDiv_and_apply_inl_one_eq_degree_sndDiv_level
    (q N : ℕ) [Fact q.Prime] [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k q] [PerfectField k] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (e : Place k (modularFunctionFieldC k N) → ℕ)
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)

    (D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hadm : ∀ V' ∈ (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
      P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨ (P.reduceFst V' ∈ W ∧ 0 < depth V' ∧ depth V' < e (P.reduceFst V')))
    (hstrict : ∀ V' ∈ (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
      ¬ (P.IsStrictFst V' ∧ P.IsStrictSnd V') ∧ (P.reduceFst V' ∈ W → ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V'))

    {node : Type} [Fintype node] [DecidableEq node] (wd : node → ℕ)
    (σN : ↥W ≃ node) (hσN : ∀ w : ↥W, wd (σN w) = e (w : Place k (modularFunctionFieldC k N)))

    {m : ℕ} (pos neg : Fin m → ℕ) (v : Fin m → X0MqComponents wd) (swap : Bool)
    (idx : Fin m ≃ ↥((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support))
    (hmult : ∀ j, ((pos j : ℤ) - (neg j : ℤ)) =
        (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hdict : ∀ j, v j =
        (if P.IsStrictFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) then (if swap then Sum.inl 1 else Sum.inl 0)
         else if P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) then (if swap then Sum.inl 0 else Sum.inl 1)
         else if hw : P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∈ W then
           DRResolvedModelPackage.chainPos wd (σN ⟨_, hw⟩)
             (if swap then wd (σN ⟨_, hw⟩) - depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
              else depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
         else Sum.inl 0))

    (Φ : X0MqComponents (widthOfPlaces (arithFrobC q k N) W e) ≃ X0MqComponents wd)
    (hΦ0 : Φ (Sum.inl 0) = if swap then Sum.inl 1 else Sum.inl 0)
    (hΦ1 : Φ (Sum.inl 1) = if swap then Sum.inl 0 else Sum.inl 1)
    (hΦr : ∀ (s : ↥(nodePairsOfPlaces (arithFrobC q k N) W)) (kk : Fin (widthOfPlaces (arithFrobC q k N) W e s - 1)) (kk' : Fin (wd (σN ((nodeEquivOfPlaces (arithFrobC q k N) W).symm s)) - 1)),
      (if swap then kk.val + kk'.val + 2 = wd (σN ((nodeEquivOfPlaces (arithFrobC q k N) W).symm s)) else kk'.val = kk.val) →
        Φ (Sum.inr ⟨s, kk⟩) = Sum.inr ⟨σN ((nodeEquivOfPlaces (arithFrobC q k N) W).symm s), kk'⟩) :
    (∀ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
      (∑ kk : Fin (widthOfPlaces (arithFrobC q k N) W e s - 1), ((kk : ℤ) + 1) *
          (∑ j, if v j = Φ (Sum.inr ⟨s, kk⟩) then ((pos j : ℤ) - (neg j : ℤ)) else 0)) =
        P.depthDiv depth (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
          ((s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1)) ∧
    ((∑ j, if v j = Φ (Sum.inl 1) then ((pos j : ℤ) - (neg j : ℤ)) else 0) =
      Divisor.degree (P.sndDiv (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))) := by sorry
