-- Prove2me | Theorems.Thm_OAI_Erdos3_jointSlicedProfileValue_unit_comparison
-- name    : OAI.Erdos3.jointSlicedProfileValue_unit_comparison
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T23:18:59.281305+00:00
-- url     : https://prove2.me/theorems/caa8a864-8a0b-4869-aeb0-55bc2aecc4cc
-- title:
--   Comparing the joint sliced profile value with its principal slice on the unit box
-- statement:
--   Let $D,G,E$ be finite types, $B\colon D\to$ Type a family of finite types with decidable equality, $h\colon D\to\mathbb N$ and `axis` $\colon E\to D$. Write $\mathrm{Input}=\Sigma_e\,B(\mathrm{axis}\,e)\times\mathrm{Fin}\,h(\mathrm{axis}\,e)$ and $\mathrm{Output}=\Sigma_{e:E}\,\mathrm{Unit}$. Let $m\in\mathbb N$ with $0<h(\mathrm{axis}\,e)\le m$ for all $e$; $\rho\colon D\to\mathbb R$; $r_e\colon$ `SamplerCoefficientSlot G B h (axis e)` $\to\mathbb R$ with $|r_e(j)|\le1$ for all $e,j$; and real polynomials $\xi_e(k)$ in the variables Input, indexed by $e\in E$ and $k\in$ `SamplerTupleIndex G B h` $=G\oplus$ `PrincipalTupleIndex B h`, each of total degree at most $1$ and with `realPolynomialMass` (the sum of the absolute values of the coefficients) at most $1$. Let `lower`, `width` assign a real number to each $e$ and each $(b,i)\in B(\mathrm{axis}\,e)\times\mathrm{Fin}\,h(\mathrm{axis}\,e)$, with $\xi_e(\mathrm{inr}\,\langle\mathrm{axis}\,e,b,i\rangle)=\mathrm{lower}_e(b,i)+\mathrm{width}_e(b,i)\,X_{\langle e,b,i\rangle}$ and $|\mathrm{lower}_e(p)|+|\mathrm{width}_e(p)|\le1$ for all $e,b,i,p$. Let $b_e\in B(\mathrm{axis}\,e)$ and $i_e\in\mathrm{Fin}\,h(\mathrm{axis}\,e)$ for each $e$, and reals $a,\delta,\eta$ with $a>0$, $0<\delta\le1$, $\eta>0$, such that $a\le$ `unitProfilePrincipalSize (axis e)` for all $e$ (a real number depending on $|B(\mathrm{axis}\,e)|$), $\delta\le\mathrm{width}_e(b_e,j)$ for all $e,j$, and $0\le\mathrm{lower}_e(b_e,j)$ whenever $j\ne i_e$. Let $A\ge0$ with `Real.smoothTransition` $A$-Lipschitz, and $t$ a real number with $|t|\cdot$ `polynomialMassC2Budget |Input| m 1` $\le$ `slicedPrincipalC2Tolerance |Input| |E| m 1 a δ A η` (explicit real numbers; the first is $(1+|\mathrm{Input}|\,m)^2$). Let $\varphi\colon(\mathrm{Output}\to\mathbb R)\to\mathbb R$ be measurable with $\|\varphi\|\le1$. Then
--   $$\Big|\int\varphi(U_1(x))\,dx-\int\varphi(U_2(x))\,dx\Big|\le\eta,$$
--   both integrals over Lebesgue measure restricted to `positiveUnitBox Input` (`mappedTest (unitBoxMeasure Input)`), where $U_1(x)=$ `jointSlicedProfileShift h axis ρ r` $+$ `jointSlicedPrincipal (jointSlicedProfilePrincipal h axis unitProfilePrincipalSize r) lower width x` and $U_2=$ `jointSlicedProfileValue h axis ρ unitProfilePrincipalSize (unitProfileTailSize h) r ξ t`. Here `jointSlicedProfileShift` is the function $o\mapsto\rho(\mathrm{axis}\,o.1)\,r_{o.1}(\texttt{constantCoefficientSlot})$; `jointSlicedProfilePrincipal γ r e b` $=\tfrac32\gamma(\mathrm{axis}\,e)+\tfrac12\gamma(\mathrm{axis}\,e)\,r_e(\texttt{principalCoefficientSlot}\ h\ (\mathrm{axis}\,e)\ b)$; `jointSlicedPrincipal` is OpenAI's `sigmaAxisSampler` of `principalSliceSingleton` samplers, a map from $\mathrm{Input}\to\mathbb R$ to $\mathrm{Output}\to\mathbb R$; and `jointSlicedProfileValue … x o` evaluates a `monomialArrayPolynomial` with coefficients built from `coefficientProfileCenter`, `coefficientProfileWidth` and $r_{o.1}$ at the values $\xi_{o.1}(k)(x)$.
--
--   Lean: `OAI.Erdos3.jointSlicedProfileValue_unit_comparison` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedEndpointIdentity.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B132` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedEndpointIdentity.lean#L135

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B174

namespace OAI

section

namespace Erdos3

open MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

variable {D G E : Type*} [Fintype D] [Fintype G] [Fintype E]
variable {B : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (axis : E → D)

local notation "Input" => (Σ e, B (axis e) × Fin (h (axis e)))
local notation "Output" => (Σ _e : E, Unit)

theorem jointSlicedProfileValue_unit_comparison
    {m : ℕ} (hh : ∀ e, 0 < h (axis e)) (hm : ∀ e, h (axis e) ≤ m)
    (ρ : D → ℝ) (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ)
    (hr : ∀ e j, |r e j| ≤ 1)
    (ξ : E → SamplerTupleIndex G B h → MvPolynomial Input ℝ)
    (hξdegree : ∀ e k, (ξ e k).totalDegree ≤ 1)
    (hξmass : ∀ e k, realPolynomialMass (ξ e k) ≤ 1)
    (lower width : ∀ e, B (axis e) × Fin (h (axis e)) → ℝ)
    (hξ : ∀ e b i, ξ e (.inr ⟨axis e, b, i⟩) =
      MvPolynomial.C (lower e (b, i)) + MvPolynomial.C (width e (b, i)) * MvPolynomial.X ⟨e, b, i⟩)
    (hwidth : ∀ e p, |lower e p| + |width e p| ≤ 1)
    (b : ∀ e, B (axis e)) (i : ∀ e, Fin (h (axis e)))
    {a δ η : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (hprincipal : ∀ e, a ≤ unitProfilePrincipalSize (B := B) (axis e))
    (hw : ∀ e j, δ ≤ width e (b e, j))
    (hlower : ∀ e j, j ≠ i e → 0 ≤ lower e (b e, j))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (t : ℝ)
    (ht : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card E) m 1 a δ A η)
    (φ : (Output → ℝ) → ℝ) (hφ : Measurable φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    |mappedTest (unitBoxMeasure Input)
        (fun x => jointSlicedProfileShift h axis ρ r +
          jointSlicedPrincipal (jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r)
            lower width x) φ -
      mappedTest (unitBoxMeasure Input)
        (jointSlicedProfileValue h axis ρ (unitProfilePrincipalSize (B := B))
          (unitProfileTailSize (G := G) (B := B) h) r ξ t) φ| ≤ η := by
  sorry

end Erdos3
end
end OAI
