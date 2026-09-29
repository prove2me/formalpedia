-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/5c3401a3-6334-5b9e-9ace-fe1aa736f359
-- title:
--   Good representative of an inertia-stable twistable class
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a level $N\ge 1$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, and integrality hypotheses $h\alpha$, $h\beta$ for the two Hecke embeddings at level $N$; let $P$ be a place specialisation for these data, assume $q \nmid N$, and let $W$ be a finite set of places of `modularFunctionFieldC k N` whose members are exactly the supersingular places `ssPlaces q N k`. Let $R$ be a prolongation tuple for $P$ which is a model and satisfies the regularity law, the node-value law, the fixed-order law and the value-integrality law at each $w \in W$, and let `dat` be a level-$N$ annulus datum for $R$ over $W$, i.e. intermediate fields $K(w)$ of $\overline{\mathbb Q}/\mathbb Q$, node coordinates $(x,y)$ over $K(w)$ at each $w\in W$, widths, a depth function `depthQ` on places of `modularFunctionFieldBar (N*q)` with values in $\mathbb Q$, uniformisers and correction divisors, and units $u_0, \lambda, \mu$ of $k$. The datum is assumed to satisfy a long normalisation block, summarised here: widths are at least $1$ and equal `placeWidthChar q N`; for $V$ reducing to $w \in W$ and strict of neither kind, $0 < \mathrm{depthQ}(V) < \mathrm{width}(w)$ and the $y$-depth of $V$, raised to the denominator of $\mathrm{depthQ}(V)$, equals $v_A(q)$ raised to the numerator; `depthQ` is invariant under the inertia subgroup of $A$ over $\mathbb Q$ acting through `arithmeticGalois`; when $\mathrm{width}(w)\ge 2$ there is an inertia-fixed $V$ over $w$, strict of neither kind, of depth $1$; the divisors of `unifFst w` and `unifSnd w` are $w$ (resp. its `arithFrobC q k N`-translate) plus a correction divisor vanishing on $W$ of degree $-1$; each $K(w)$ is pointwise fixed by inertia and finite over $\mathbb Q$; elements $\varpi(w)$, exponents $e_K(w)\ge 1$, units $\varepsilon(w)$ of the coefficient subring `NodeLocalized.coeffSubring A (K w)` and units $u(w)$ of `R.nodeIntegersOver (K w) w` satisfy that $\varpi(w)$ generates the kernel of `NodeLocalized.redRestrict red (K w)`, $q = \varpi(w)^{e_K(w)}\varepsilon(w)$ with $\varepsilon(w)$ reducing to $1$, and $xy = \varpi(w)^{\mathrm{width}(w)e_K(w)}u(w)$ after applying `R.nodeConst`; the ideal spanned by $\varpi(w), x, y$ is the unique maximal ideal of `R.nodeIntegersOver (K w) w`, the two branch ideals spanned by $\varpi(w)$ together with $x$, resp. $y$, are prime with $y$, resp. $x$, outside them, that ring is Noetherian and no element becomes a unit after subtracting a suitable constant; and $u(w)$, $y/\mathrm{unifFst}(w)$, $x/\mathrm{unifSnd}(w)$ have residues $u_0(w)$, $\lambda(w)$, $\mu(w)$ at $w$, resp. at the Frobenius translate of $w$, computed through `R.nodeResidue₁`, `R.nodeResidue₂`. Finally let $X$ be a degree-zero divisor on `modularFunctionFieldBar (N*q)` over $\overline{\mathbb Q}$ which is fixed by every inertia element acting through `arithmeticGalois`, each place of whose support is strict of the first or second kind for $P$ or reduces under `P.reduceFst` into $W$, let $a$ be a level-$N$ twist vector over $W$ with `dat.IsTwistOf a X`, and assume the twisted gluing datum `dat.spData a X` is admissible for the node pairs $\{(w, \mathrm{arithFrobC}\cdot w) : w \in W\}$ and has class zero in `GluedPic0`. Then there is a degree-zero divisor $D_2$ on `modularFunctionFieldBar (N*q)` such that the plain gluing datum `P.glueData` of $D_2$ (the two pushed-forward divisors with trivial unit component) is admissible, every place in the support of $D_2$ is strict of the first or second kind for $P$, the class of `P.glueData` of $D_2$ in `GluedPic0` is zero, and $D_2$ and $X$ have the same class in $\mathrm{Pic}^0$.
--
--   This is the representability step in Raynaud's description of the special fibre of the Jacobian of $X_0(Nq)$ at $q \nmid N$: a degree-zero class whose twisted specialisation to the glued Picard group of the Deligne–Rapoport fibre vanishes admits a representative supported entirely on the strict places, with vanishing untwisted glued datum. It is the level-$N$ form of the corresponding statement for the annulus datum at level one, and feeds into [`ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_fixedStrict_add_kernelGood_of_isTwistOf_of_inertiaStable`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_fixedStrict_add_kernelGood_of_isTwistOf_of_inertiaStable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.lean

import Mathlib
import Definitions.Def_ModularCurve_AnnulusSpecializationLevel
import Definitions.Def_ModularCurve_PlaceWidthChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open AlgebraicCurve
open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k (modularFunctionFieldC k N))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed) (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)
    (dat : R.AnnulusDatumLevel W)
    (hwidth : ∀ w ∈ W, 1 ≤ dat.width w)
    (hwidthc : ∀ w ∈ W, dat.width w = placeWidthChar q N w)
    (hdepthQ : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
      (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
      A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (dat.depthQ V).num.toNat)
    (hdepthσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      dat.depthQ (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = dat.depthQ V)
    (hD1 : ∀ w ∈ W, 2 ≤ dat.width w → ∃ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧ dat.depthQ V = 1)
    (hunif : ∀ w ∈ W,
      ((∀ v, (Finsupp.single w (1 : ℤ) + dat.corrFst w) v = v.ord (dat.unifFst w)) ∧ (∀ v ∈ W, dat.corrFst w v = 0) ∧
      Divisor.degree (dat.corrFst w) = -1) ∧
      ((∀ v, (Finsupp.single (arithFrobC q k N • w) (1 : ℤ) + dat.corrSnd w) v = v.ord (dat.unifSnd w)) ∧
      (∀ v ∈ W, dat.corrSnd w v = 0) ∧ Divisor.degree (dat.corrSnd w) = -1))
    (hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ dat.K w, σ z = z)
    (hK : ∀ w : Place k (modularFunctionFieldC k N), FiniteDimensional ℚ ↥(dat.K w))
    (ϖ : ∀ w : Place k (modularFunctionFieldC k N), ↥(NodeLocalized.coeffSubring A (dat.K w)))
      (eK : Place k (modularFunctionFieldC k N) → ℕ)
      (ε : ∀ w : Place k (modularFunctionFieldC k N), ↥(NodeLocalized.coeffSubring A (dat.K w)))
      (u : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), ↥(R.nodeIntegersOver (dat.K w) w))
    (hϖ : ∀ w ∈ W, ∀ d : ↥(NodeLocalized.coeffSubring A (dat.K w)),
      NodeLocalized.redRestrict red (dat.K w) d = 0 ↔ ∃ d', d = ϖ w * d')
    (heK : ∀ w ∈ W, 1 ≤ eK w)
    (hε : ∀ w ∈ W, IsUnit (ε w))
    (hqϖ : ∀ w ∈ W, ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (dat.K w))) = ϖ w ^ eK w * ε w)
    (hε1 : ∀ w ∈ W, NodeLocalized.redRestrict red (dat.K w) (ε w) = 1)
    (hu : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), IsUnit (u w hw) ∧
      (dat.coord w hw).x * (dat.coord w hw).y = R.nodeConst (dat.K w) w (ϖ w) ^ (dat.width w * eK w) * u w hw)
    (hmax : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver (dat.K w) w), M.IsMaximal →
      M = Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y})
    (hbr : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x}).IsPrime ∧
      (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y}).IsPrime ∧
      (dat.coord w hw).y ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x} ∧
      (dat.coord w hw).x ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y})
    (hnoeth : ∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver (dat.K w) w))
    (hres : ∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver (dat.K w) w),
      ∃ o : ↥(NodeLocalized.coeffSubring A (dat.K w)), ¬ IsUnit (g - R.nodeConst (dat.K w) w o))
    (hu0 : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨(u w hw : ↥(modularFunctionFieldBar (N * q))), (u w hw).2.1⟩) ((dat.u0 w : kˣ) : k))
    (hlam : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨((dat.coord w hw).y : ↥(modularFunctionFieldBar (N * q))), (dat.coord w hw).y.2.1⟩
      / dat.unifFst w) ((dat.lam w : kˣ) : k))
    (hmu : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      (arithFrobC q k N • w).HasValue
      (R.nodeResidue₂ w ⟨((dat.coord w hw).x : ↥(modularFunctionFieldBar (N * q))), (dat.coord w hw).x.2.1⟩
      / dat.unifSnd w) ((dat.mu w : kˣ) : k))
    (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hXstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = X)
    (hXsupp : ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)
    (a : ProlongationTuple.TwistVectorLevel (k := k) (N := N) W)
    (ha : dat.IsTwistOf a (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hadm : dat.spData a (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W))
    (hsp : GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N) W) ⟨dat.spData a (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), hadm⟩ = 0) :
    ∃ (D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
      (hadm₂ : P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W)),
      P.IsGoodDiv (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∧
      GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N) W) ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), hadm₂⟩ = 0 ∧
      Pic0.mk D₂ = Pic0.mk X := by sorry
