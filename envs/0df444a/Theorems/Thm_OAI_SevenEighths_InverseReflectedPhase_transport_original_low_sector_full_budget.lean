-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseReflectedPhase_transport_original_low_sector_full_budget
-- name    : OAI.SevenEighths.InverseReflectedPhase.transport_original_low_sector_full_budget
-- status  : Proved
-- author  : @Himan
-- created : 2026-11-15T17:47:40.35761+00:00
-- url     : https://prove2.me/theorems/ba73afd4-0ad6-4d26-a6c3-6bdf10c5f472
-- title:
--   Low sector whole rows with the full budget, for total slot width $E\le1/5$
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
--   **Statement.** Let $\varepsilon>0$, let $W$ be smooth with support in $[lo,hi]$, $lo>0$, and fix a cusp shape with $c_0\ne0$, $9c_0\mid N_{\mathrm{level}}$, the base congruence, $a,c_0$ coprime, and $\rho,\eta,\kappa,\delta>0$, $\delta+L_{\mathrm{scale}}\ge0$, $L_{\mathrm{pool}}\ge0$, and reals $L_{\mathrm{cap}}$, $\mathrm{saving}$. There are a degree $D\in\mathbb N$, $C>0$ and $Z_0>1$ such that, for all data as in the Lean statement and all real parameters satisfying its size conditions, in particular
--   $$
--   N(I)\le C_k\,Z^{\,1-E-2d},\qquad 0\le d\le E,\qquad \ell_0\le E-d+\eta ,
--   $$
--   $$
--   -\mathrm{saving}\le(1-E-2d)+\lambda(E,d)+200\eta+\pi+\kappa+\rho L_{\mathrm{pool}}-\tfrac{O_0}2 ,
--   $$
--   one has
--   $$
--   \sum_{K\in\mathrm{rows}}\big\lVert\texttt{literalWholeRow}(\dots;W,\theta,X,r,a_w)\big\rVert^2\le C\,(1+|\theta|)^{D}\,Z^{\,(1-E-2d)+\lambda(E,d)+200\eta+\pi+\kappa+\rho L_{\mathrm{pool}}-O_0/2}.
--   $$
--
--   This passes from the retained dyads to the whole rows: the dyads that are not retained are bounded by the saving hypothesis, and the number of retained dyads and the pool norm are absorbed in $Z^{\kappa+\rho L_{\mathrm{pool}}}$.
--
--   **Relation to the fixed-width statement.** For $E=\tfrac16$ this is OpenAI's Proved theorem `OAI.SevenEighths.InverseReflectedPhase.original_low_sector_full_budget`. The statement here differs from it only as follows: $\tfrac56$ is replaced by $1-E$ and $\tfrac16$ by $E$ in the hypotheses on the row length, on $d$ and on $\ell_0$, and the term $\lambda(E,d)$ is added to the exponent of $Z$ in the saving hypothesis and in the conclusion. All other hypotheses and all objects are unchanged.
--
--   **Formalization Note** `RH.Transport.Reflected.reflectedLoss totalWidth d` is $\lambda(E,d)$. The remaining definitions are OpenAI's, from the definition bundles of the OpenAI mission on this platform. Spaces were inserted after some `<` and `≤` signs so that the statement tokenizes under `import Mathlib`; the statement is otherwise verbatim from the source.
-- source:
--   LW56e2, quasi-riemann-improved, commit b83dbbd914c5751acf9bc3389cde58970437278f, lean/Transport/PhysicalLow/LowFullBudget.lean, theorem transport_original_low_sector_full_budget (L21-L68): https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/PhysicalLow/LowFullBudget.lean#L21-L68

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

variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem transport_original_low_sector_full_budget (totalWidth : ℝ) (hE0 : 0≤ totalWidth) (hE1 : totalWidth≤1/5)
    (ε : ℝ) (hε : 0< ε) (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0< ρ) (η : ℝ) (hηpos : 0< η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0< κ) (hδL : 0≤ δ+Lscale) (hLpool : 0≤ Lpool)
    (Lcap saving : ℝ) (hδ : 0< δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0< C ∧ 1< Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
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
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤ QK → 2≤ QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤ QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤ QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^((1-totalWidth-2*d)+RH.Transport.Reflected.reflectedLoss totalWidth d+200*η+π+κ+ρ*Lpool-O₀/2) := by sorry

end
end SevenEighths.InverseReflectedPhase

end OAI
