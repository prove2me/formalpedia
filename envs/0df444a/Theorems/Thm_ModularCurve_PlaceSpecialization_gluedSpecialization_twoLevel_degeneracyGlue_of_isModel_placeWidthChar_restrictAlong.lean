-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_gluedSpecialization_twoLevel_degeneracyGlue_of_isModel_placeWidthChar_restrictAlong
-- name    : ModularCurve.PlaceSpecialization.gluedSpecialization_twoLevel_degeneracyGlue_of_isModel_placeWidthChar_restrictAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/7423fa88-5ec4-53c1-a276-05c7b5ae950a
-- title:
--   Two-level degeneracy glue for glued specialisations at q'
-- statement:
--   Fix natural numbers $M, s, q'$ with $M$ and $s$ nonzero, $s$ and $q'$ prime, $s \neq q'$, and neither $q'$ nor $s$ dividing $M$. Fix a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $q'$ in the sense of `LiesOverPrime`, i.e. $q'$ is a non-unit of $A$; consequently its residue field $\kappa =$ `ResidueField A` has characteristic $q'$. The `HeckeAlg`-module structures `heckeModuleBar` on $J_0$ at the levels $(Ms)q'$, $Ms$, $Mq'$ and $M$, decidable equality on $\kappa$, and the $\kappa$-algebra structures on the function fields `modularFunctionFieldC κ (M * s)` and `modularFunctionFieldC κ M` are the ones fixed by the semistable-setting instances; finiteness and decidable equality of the two sets `ssPlaces q' (M * s) κ` and `ssPlaces q' M κ` of places satisfying `IsSupersingularPlace` are assumed.
--
--   Two packages of data are given, one at level $Ms$ (subscript $1$) and one at level $M$ (subscript $2$), of identical shape; here $S_1 =$ `nodePairsOfPlaces (arithFrobC q' κ (M * s)) W₁` denotes the finset of node pairs $(w, \mathrm{Frob}\cdot w)$ obtained from $W_1$ by `smulNodePair` for the semilinear automorphism `arithFrobC q' κ (M * s)` of `modularFunctionFieldC κ (M * s)` acting on coefficients through the $q'$-power Frobenius of $\kappa$, and similarly $S_2$ at level $M$. The level-$Ms$ package consists of: a finset $W_1$ of places of `modularFunctionFieldC κ (M * s)` whose members are exactly the places in `ssPlaces q' (M * s) κ` (hypothesis `hW₁`); the hypothesis `hstab₁` that $S_1$ is node-stable for `arithFrobC q' κ (M * s)`, i.e. $(\mathrm{Frob}\cdot a, \mathrm{Frob}\cdot b) \in S_1$ for every $(a,b) \in S_1$; a modular polynomial datum `data₁ : ModularPolynomialData q'` together with the Kronecker congruence `hKr₁`, asserting that the bivariate reduction of its polynomial $\Phi$ is $(C(X)^{q'} - X)(C(X) - X^{q'})$; the integrality hypotheses `hα₁`, `hβ₁` for the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` from level $Ms$ to level $(Ms)q'$ over $\overline{\mathbb{Q}}$; a place-specialisation package $P_1$ of type `PlaceSpecialization A q' (M * s) data₁ hKr₁ κ (IsLocalRing.residue A) hα₁ hβ₁`; a prolongation tuple $R_1$ for $P_1$ with `hmodel₁ : R₁.IsModel` (the conjunction of the two divisor laws and the two cusp laws at $\infty$ and at $0$) and `hO₁ : R₁.OrderLawFixed` (the order law at the affine geometric places fixed by the square of `frobOnPlacesGeomLevel`); a width function $e_1$ on places of `modularFunctionFieldC κ (M * s)`, positive on $W_1$ (`he₁`) and pinned on $W_1$ to the characteristic-$q'$ width, $e_1(w) =$ `placeWidthChar q' (M * s) w` (`hpin₁`); additive maps
--   $$\mathrm{comp}_1 : \mathrm{inertiaInvariants}\,A\,((Ms)q') \to \mathrm{componentGroup}(\mathrm{widthOfPlaces}\,(\mathrm{arithFrobC}\,q'\,\kappa\,(Ms))\,W_1\,e_1),$$
--   $$\mathrm{sp}_1 : \mathrm{inertiaInvariants}\,A\,((Ms)q') \to \mathrm{GluedPic}^0(\kappa, \mathrm{modularFunctionFieldC}\,\kappa\,(Ms), S_1),$$
--   where the source is the subgroup of $J_0((Ms)q')$ fixed by the inertia subgroup of $A$ over $\mathbb{Q}$, the component group is the dual of the character lattice modulo the image of the Gram map for the width function sending a node pair to the $e_1$-value of its first component, and `GluedPic0` is the group of admissible gluing data modulo glued-principal ones; and the three hypotheses that $\mathrm{comp}_1$ is surjective (`hsurj₁`), that $\mathrm{comp}_1 x = 0$ holds exactly for those $x$ whose underlying class in $J_0((Ms)q')$ is a $P_1$-good class for $S_1$ (`hker₁`: there is a degree-zero divisor $D$ on the level-$(Ms)q'$ curve over $\overline{\mathbb{Q}}$, supported at places that are strictly-first or strictly-second for $P_1$, with `glueData` admissible and class equal to $x$), and that $\mathrm{sp}_1$ is a glued specialisation for $P_1$ and $S_1$ (`hsp₁`: for every degree-zero $D$ whose class lies in the inertia invariants and which is $P_1$-good, and every admissible gluing datum equal to $P_1.\mathrm{glueData}\,S_1\,D$, the value of $\mathrm{sp}_1$ at the class of $D$ is the class of that gluing datum). The level-$M$ package $(W_2, \mathrm{hW}_2, \mathrm{hstab}_2, \mathrm{data}_2, \mathrm{hKr}_2, h\alpha_2, h\beta_2, P_2, R_2, \mathrm{hmodel}_2, hO_2, e_2, \mathrm{he}_2, \mathrm{hpin}_2, \mathrm{comp}_2, \mathrm{sp}_2, \mathrm{hsurj}_2, \mathrm{hker}_2, \mathrm{hsp}_2)$ is of exactly the same shape with $Ms$ replaced by $M$ and $(Ms)q'$ by $Mq'$.
--
--   Under these hypotheses there exist a pair of maps $ab : \mathrm{Fin}\,2 \to (\mathrm{ssPlaces}\,q'\,(Ms)\,\kappa \to \mathrm{ssPlaces}\,q'\,M\,\kappa)$, positive-integer width functions $w$ on `ssPlaces q' (M * s) κ` and $wV$ on `ssPlaces q' M κ`, multiplicities $m : \mathrm{Fin}\,2 \to \mathrm{ssPlaces}\,q'\,(Ms)\,\kappa \to \mathbb{N}$, and additive maps $\Phi_i : \mathrm{GluedPic}^0(\kappa, \mathrm{modularFunctionFieldC}\,\kappa\,(Ms), S_1) \to \mathrm{GluedPic}^0(\kappa, \mathrm{modularFunctionFieldC}\,\kappa\,M, S_2)$ for $i \in \mathrm{Fin}\,2$, such that the following eight assertions hold.
--
--   First, $w(p) = e_1(p)$ for every $p \in \mathrm{ssPlaces}\,q'\,(Ms)\,\kappa$, and second, $wV(v) = e_2(v)$ for every $v \in \mathrm{ssPlaces}\,q'\,M\,\kappa$, as natural numbers.
--
--   Third, for each $i \in \mathrm{Fin}\,2$, each $x$ in the inertia invariants of $J_0((Ms)q')$, each $z \in J_0((Mq')s)$ which is the transport of $x$ along the identification of levels given by $M \cdot s \cdot q' = M \cdot q' \cdot s$, and each proof that `degeneracyPushforwardPair (M * q') s i z` lies in the inertia invariants of $J_0(Mq')$: if $\mathrm{comp}_1 x = 0$ then $\mathrm{comp}_2$ of that pushforward class is $0$. Fourth, for the same data, if in addition $\mathrm{comp}_1 x = 0$ and $\mathrm{comp}_2$ of the pushforward vanishes, then $\mathrm{sp}_2$ of the pushforward class equals $\Phi_i(\mathrm{sp}_1 x)$; here `degeneracyPushforwardPair (M * q') s` is the pair of pushforwards along `heckeAlphaBar` and `heckeBetaBar` from level $(Mq')s$ to level $Mq'$.
--
--   Fifth, $m_i(p) \cdot w(p) = wV(ab_i(p))$ for all $i$ and all $p$. Sixth, for all $i$ and every $v \in \mathrm{ssPlaces}\,q'\,M\,\kappa$, the sum of $m_i(p)$ over those $p$ with $ab_i(p) = v$ equals $s + 1$.
--
--   Seventh, each $\Phi_i$ is computed on node units by the weighted fibre sum: for every $g : S_1 \to \mathrm{Additive}\,\kappa^{\times}$,
--   $$\Phi_i\big(\mathrm{nodeUnit}\,S_1\,g\big) = \mathrm{nodeUnit}\,S_2\Big(n_2 \mapsto \sum_{p_1 \,:\, ab_i(p_1) = \mathrm{fst}(n_2)} m_i(p_1) \cdot g\big(\mathrm{smulNodePair}\,(\mathrm{arithFrobC}\,q'\,\kappa\,(Ms))\,p_1\big)\Big),$$
--   where $\mathrm{fst}(n_2)$ is the first component of the node pair $n_2 \in S_2$, regarded as an element of $\mathrm{ssPlaces}\,q'\,M\,\kappa$ via $\mathrm{hW}_2$, and $\mathrm{smulNodePair}\,g\,p_1 = (p_1, g \cdot p_1)$ is the node pair of $S_1$ attached to $p_1$ via $\mathrm{hW}_1$.
--
--   Eighth, the pair $ab$ is the pair of place-restriction maps along the degeneracy maps in characteristic $q'$: for every family $\varphi : \mathrm{Fin}\,2 \to (\mathrm{modularFunctionFieldC}\,\kappa\,M \to_{\mathrm{alg}[\kappa]} \mathrm{modularFunctionFieldC}\,\kappa\,(Ms))$ whose members are integral ring homomorphisms (`hφ`), such that $\varphi_0$ induces the identity on Laurent series and $\varphi_1$ induces $\mathrm{qExpand}\,\kappa\,s$, one has $\mathrm{Place.restrictAlong}\,(\varphi_i)\,(\mathrm{h}\varphi\,i)\,p = ab_i(p)$ for every $i \in \mathrm{Fin}\,2$ and every $p \in \mathrm{ssPlaces}\,q'\,(Ms)\,\kappa$.
--
--   This is the cross-level compatibility statement that ties together two independently given glued-specialisation packages for the special fibres at $q'$ of the level-$Ms$ and level-$M$ modular curves: the two degeneracy pushforwards $\alpha_*, \beta_* : J_0((Ms)q') \to J_0(Mq')$ carry good classes to good classes, transport the toric (glued Picard) part through maps $\Phi_i$ computed on node units by a weighted sum over the fibres of the degeneracy maps on supersingular places, and match the characteristic-$q'$ widths by the relation $m_i(p) \, w(p) = wV(ab_i(p))$ with fibre degrees $s+1$. It is the cross-level ingredient of the two Čerednik–Drinfeld joint-construction statements that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_gluedSpecialization_twoLevel_degeneracyGlue_of_isModel_placeWidthChar_restrictAlong.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.gluedSpecialization_twoLevel_degeneracyGlue_of_isModel_placeWidthChar_restrictAlong
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) (hq' : q'.Prime)
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q') :
    haveI : NeZero q' := ⟨hq'.ne_zero⟩
    haveI : Fact q'.Prime := ⟨hq'⟩
    haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
    letI := heckeModuleBar ((M * s) * q')
    letI := heckeModuleBar (M * s)
    letI := heckeModuleBar (M * q')
    letI := heckeModuleBar M
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
    ∀ [Fintype ↥(ssPlaces q' (M * s) (ResidueField A))]
      [Fintype ↥(ssPlaces q' M (ResidueField A))]
      [DecidableEq ↥(ssPlaces q' (M * s) (ResidueField A))]
      [DecidableEq ↥(ssPlaces q' M (ResidueField A))],
    ∀ (W₁ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s))))
      (hW₁ : ∀ w, w ∈ W₁ ↔ w ∈ ssPlaces q' (M * s) (ResidueField A))
      (hstab₁ : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (arithFrobC q' (ResidueField A) (M * s)))
      (data₁ : ModularPolynomialData q') (hKr₁ : KroneckerCongruence q' data₁)
      (hα₁ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (M * s) q')
      (hβ₁ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (M * s) q')
      (P₁ : PlaceSpecialization A q' (M * s) data₁ hKr₁ (ResidueField A) (IsLocalRing.residue A) hα₁ hβ₁)
      (R₁ : PlaceSpecialization.ProlongationTuple P₁) (hmodel₁ : R₁.IsModel) (hO₁ : R₁.OrderLawFixed)
      (e₁ : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s)) → ℕ)
      (he₁ : ∀ p ∈ W₁, 0 < e₁ p)
      (hpin₁ : ∀ w ∈ W₁, e₁ w = placeWidthChar q' (M * s) w)
      (comp₁ : ↥(inertiaInvariants A ((M * s) * q')) →+
        componentGroup (widthOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁ e₁))
      (sp₁ : ↥(inertiaInvariants A ((M * s) * q')) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s))
          (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁))
      (hsurj₁ : Function.Surjective comp₁)
      (hker₁ : ∀ x : ↥(inertiaInvariants A ((M * s) * q')),
        comp₁ x = 0 ↔ P₁.IsGoodClass (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (x : JZero ((M * s) * q')))
      (hsp₁ : P₁.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) sp₁),
    ∀ (W₂ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M))))
      (hW₂ : ∀ w, w ∈ W₂ ↔ w ∈ ssPlaces q' (M) (ResidueField A))
      (hstab₂ : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂) (arithFrobC q' (ResidueField A) (M)))
      (data₂ : ModularPolynomialData q') (hKr₂ : KroneckerCongruence q' data₂)
      (hα₂ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (M) q')
      (hβ₂ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (M) q')
      (P₂ : PlaceSpecialization A q' (M) data₂ hKr₂ (ResidueField A) (IsLocalRing.residue A) hα₂ hβ₂)
      (R₂ : PlaceSpecialization.ProlongationTuple P₂) (hmodel₂ : R₂.IsModel) (hO₂ : R₂.OrderLawFixed)
      (e₂ : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M)) → ℕ)
      (he₂ : ∀ p ∈ W₂, 0 < e₂ p)
      (hpin₂ : ∀ w ∈ W₂, e₂ w = placeWidthChar q' M w)
      (comp₂ : ↥(inertiaInvariants A ((M) * q')) →+
        componentGroup (widthOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂ e₂))
      (sp₂ : ↥(inertiaInvariants A ((M) * q')) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) (M))
          (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂))
      (hsurj₂ : Function.Surjective comp₂)
      (hker₂ : ∀ x : ↥(inertiaInvariants A ((M) * q')),
        comp₂ x = 0 ↔ P₂.IsGoodClass (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂) (x : JZero ((M) * q')))
      (hsp₂ : P₂.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂) sp₂),
      ∃ (ab : Fin 2 → (↥(ssPlaces q' (M * s) (ResidueField A)) →
            ↥(ssPlaces q' M (ResidueField A))))
        (w : ↥(ssPlaces q' (M * s) (ResidueField A)) → ℕ+)
        (wV : ↥(ssPlaces q' M (ResidueField A)) → ℕ+)
        (m : Fin 2 → ↥(ssPlaces q' (M * s) (ResidueField A)) → ℕ)
        (Φ : Fin 2 → (GluedPic0 (ResidueField A)
              (modularFunctionFieldC (ResidueField A) (M * s)) (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) →+
            GluedPic0 (ResidueField A)
              (modularFunctionFieldC (ResidueField A) M) (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂))),
        (∀ p : ↥(ssPlaces q' (M * s) (ResidueField A)), (w p : ℕ) = e₁ ↑p) ∧
        (∀ v : ↥(ssPlaces q' M (ResidueField A)), (wV v : ℕ) = e₂ ↑v) ∧
        (∀ (i : Fin 2) (x : ↥(inertiaInvariants A ((M * s) * q')))
            (z : JZero ((M * q') * s))
            (_ : Nat.mul_right_comm M s q' ▸ (x : JZero ((M * s) * q')) = z)
            (hx : degeneracyPushforwardPair (M * q') s i z ∈ inertiaInvariants A (M * q')),
            comp₁ x = 0 →
              comp₂ ⟨degeneracyPushforwardPair (M * q') s i z, hx⟩ = 0) ∧
        (∀ (i : Fin 2) (x : ↥(inertiaInvariants A ((M * s) * q')))
            (z : JZero ((M * q') * s))
            (_ : Nat.mul_right_comm M s q' ▸ (x : JZero ((M * s) * q')) = z)
            (hx : degeneracyPushforwardPair (M * q') s i z ∈ inertiaInvariants A (M * q')),
            comp₁ x = 0 →
              comp₂ ⟨degeneracyPushforwardPair (M * q') s i z, hx⟩ = 0 →
                sp₂ ⟨degeneracyPushforwardPair (M * q') s i z, hx⟩ = Φ i (sp₁ x)) ∧
        (∀ (i : Fin 2) (p : ↥(ssPlaces q' (M * s) (ResidueField A))),
            m i p * (w p : ℕ) = (wV (ab i p) : ℕ)) ∧
        (∀ (i : Fin 2) (v : ↥(ssPlaces q' M (ResidueField A))),
            (∑ p with ab i p = v, m i p) = s + 1) ∧
        (∀ (i : Fin 2) (g : ↥(nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) → Additive (ResidueField A)ˣ),
            Φ i (GluedPic0.nodeUnit (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) g) =
              GluedPic0.nodeUnit (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)
                (fun n₂ => ∑ p₁ with ab i p₁ =
                    (⟨(↑n₂ : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M) ×
                        Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M)).1,
                      (hW₂ _).mp (fst_mem_of_mem_nodePairsOfPlaces n₂.2)⟩ :
                      ↥(ssPlaces q' M (ResidueField A))),
                  m i p₁ • g ⟨smulNodePair (arithFrobC q' (ResidueField A) (M * s)) ↑p₁,
                    smulNodePair_mem_nodePairsOfPlaces _ ((hW₁ ↑p₁).mpr p₁.2)⟩)) ∧
        (∀ (φ : Fin 2 → (↥(modularFunctionFieldC (IsLocalRing.ResidueField A) M) →ₐ[IsLocalRing.ResidueField A]
                ↥(modularFunctionFieldC (IsLocalRing.ResidueField A) (M * s))))
            (hφ : ∀ i, (φ i).toRingHom.IsIntegral),
            (∀ x, ((φ 0 x : ↥(modularFunctionFieldC (IsLocalRing.ResidueField A) (M * s))) :
                LaurentSeries (IsLocalRing.ResidueField A)) = x) →
            (∀ x, ((φ 1 x : ↥(modularFunctionFieldC (IsLocalRing.ResidueField A) (M * s))) :
                LaurentSeries (IsLocalRing.ResidueField A)) = qExpand (IsLocalRing.ResidueField A) s x) →
            ∀ (i : Fin 2) (p : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A))),
              AlgebraicCurve.Place.restrictAlong (φ i) (hφ i) (↑p) = ↑(ab i p)) := by sorry
