-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseReflectedPhase_transport_original_low_member_geometry_uniform
-- name    : OAI.SevenEighths.InverseReflectedPhase.transport_original_low_member_geometry_uniform
-- status  : Proved
-- author  : @Himan
-- created : 2026-11-15T17:47:36.340925+00:00
-- url     : https://prove2.me/theorems/d2e07884-2aec-442e-b401-797da88c8342
-- title:
--   Low member tuple rows with a saving uniform in the geometry, for total slot width $E\le1/5$
-- statement:
--   Throughout, $\mathcal O=\mathbb Z[\zeta_3]$ is the ring of Eisenstein integers and all objects named in typewriter font are those of OpenAI's family-003 development (the zero-free half-plane $\operatorname{Re}s>7/8$ for Hecke $L$-functions of $\mathbb Q(\zeta_3)$). The parameter $E$ (`totalWidth`) is the total width of the prime slots, with
--   $$
--   0\le E\le\tfrac15 ,
--   $$
--   so that rows have length $Z^{1-E}$. OpenAI's development fixes $E=\tfrac16$. The reflected loss is
--   $$
--   \lambda(E,d)=\tfrac14\max\big(0,\;5E-1+d\big),
--   $$
--   which vanishes for $E=\tfrac16$ and $0\le d\le\tfrac16$.
--
--   **Statement.** Let $(a_i,c_{0,i},\mathrm{mode}_i)_{i\in\gamma}$ be a finite family of cusp data with fixed cusp shapes, $c_{0,i}\ne0$, $9c_{0,i}\mid N_{\mathrm{level}}$, the base congruences and $a_i,c_{0,i}$ coprime. Let $\varepsilon>0$, $W$ smooth with support in $[lo,hi]$, $lo>0$, and $\rho,\eta,\kappa,\delta>0$, $\delta+L_{\mathrm{scale}}\ge0$, $L_{\mathrm{pool}}\ge0$, and reals $L_{\mathrm{cap}}$, $\mathrm{saving}$. There are a degree $D\in\mathbb N$, $C>0$ and $Z_0>1$ such that for every $i\in\gamma$, all data as in the Lean statement (rows of norm in $[Q_K/2,Q_K]$, tuples of maximal primes with admissible products of norm in $[Q_P/2,Q_P]$, weights bounded by $1$) and all real parameters satisfying its size conditions, in particular
--   $$
--   N(I)\le C_k\,Z^{\,1-E-2d},\qquad 0\le d\le E,\qquad \ell_0\le E-d+\eta ,
--   $$
--   there is controlled stratum arithmetic data $\mathcal D$ for the reflected families with
--   $$
--   \sum_{K\in\mathrm{rows}}\big\lVert\texttt{memberTupleRow}(\dots;\mathcal D_K;W,\theta,X,r,a_w)\big\rVert^2\le C\,(1+|\theta|)^{D}\,Z^{\,(1-E-2d)+\lambda(E,d)+200\eta+\pi+\kappa+\rho L_{\mathrm{pool}}-O_0/2}.
--   $$
--
--   The constants are uniform over the finite family of cusps and over the geometry of the tuples.
--
--   **Relation to the fixed-width statement.** For $E=\tfrac16$ this is OpenAI's Proved theorem `OAI.SevenEighths.InverseReflectedPhase.original_low_member_geometry_uniform`. The statement here differs from it only as follows: $\tfrac56$ is replaced by $1-E$ and $\tfrac16$ by $E$ in the hypotheses on the row length, on $d$ and on $\ell_0$, and the term $\lambda(E,d)$ is added to the exponent of $Z$ in the saving hypothesis and in the conclusion. All other hypotheses and all objects are unchanged.
--
--   **Formalization Note** `RH.Transport.Reflected.reflectedLoss totalWidth d` is $\lambda(E,d)$. The remaining definitions are OpenAI's, from the definition bundles of the OpenAI mission on this platform. Spaces were inserted after some `<` and `≤` signs so that the statement tokenizes under `import Mathlib`; the statement is otherwise verbatim from the source.
-- source:
--   LW56e2, quasi-riemann-improved, commit b83dbbd914c5751acf9bc3389cde58970437278f, lean/Transport/PhysicalLow/LowMemberGeometry.lean, theorem transport_original_low_member_geometry_uniform (L22-L82): https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/PhysicalLow/LowMemberGeometry.lean#L22-L82

import Mathlib
import Definitions.Def_OAIHecke78B026
import Definitions.Def_OAIHecke78B028
import Definitions.Def_Transport_ReflectedExponent
set_option autoImplicit false

namespace OAI

namespace SevenEighths.InverseReflectedPhase

open scoped Classical BigOperators ContDiff

open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment

noncomputable section

local notation "Eis" => ActualEisensteinCubic.O

universe v

variable {Nlevel : Eis}

theorem transport_original_low_member_geometry_uniform (totalWidth : ℝ) (hE0 : 0≤ totalWidth) (hE1 : totalWidth≤1/5)
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0< ε) (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i)) (ρ : ℝ) (hρ : 0< ρ) (η : ℝ) (hηpos : 0< η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0< κ) (hδL : 0≤ δ+Lscale) (hLpool : 0≤ Lpool)
    (Lcap saving : ℝ) (hδ : 0< δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0< C ∧ 1< Z₀ ∧
    ∀ i : γ,
      let a := a i
      let c₀ := c₀ i
      let mode := mode i
      let s := s i
      let hc₀ := hc₀ i
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤ Z → 0< Ck → 0< CO → 0< CH → 0< X → 0< QK → 0< QP →
      (Ideal.absNorm I:ℝ)≤ Ck*Z^(1-totalWidth-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤ η →
      normWidth Z (rowPowerfulPart I)≤ O₀+η → normWidth Z Q≤ η →
      0≤ d → d≤ totalWidth → ell0≤ totalWidth-d+η → 0≤ O₀ → za≤ ell0+η → |shift|≤ η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤ δ → δ≤ η → QK≤ Z^Lrow → (QP/2)≤ Z^Lslot →
      Real.logb Z 16≤ η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤ π →
      X⁻¹≤ Z^Lcap → QK≤ Z^Lcap → QP≤ Z^Lcap → -saving≤(1-totalWidth-2*d)+RH.Transport.Reflected.reflectedLoss totalWidth d+200*η+π+κ+ρ*Lpool-O₀/2 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤ Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤ Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤ Z^Lpool →
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      ∀ (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      1≤ QK → 2≤ QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤ QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤ QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^((1-totalWidth-2*d)+RH.Transport.Reflected.reflectedLoss totalWidth d+200*η+π+κ+ρ*Lpool-O₀/2) := by sorry

end
end SevenEighths.InverseReflectedPhase

end OAI
