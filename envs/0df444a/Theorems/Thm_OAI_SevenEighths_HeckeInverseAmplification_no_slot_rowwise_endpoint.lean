-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckeInverseAmplification_no_slot_rowwise_endpoint
-- name    : OAI.SevenEighths.HeckeInverseAmplification.no_slot_rowwise_endpoint
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:09:59.265192+00:00
-- url     : https://prove2.me/theorems/9f676113-f2ec-4936-b049-e45a49ac39f1
-- title:
--   Rowwise endpoint bound for inverse polynomials without slots
-- statement:
--   Let $M\ne0$, $H\supseteq$`globalUnits M`, $S$ a finite set of ideals, $\varphi$ smooth, compactly supported, nonnegative, nonzero, with support in $(a,b)\subseteq(0,\infty)$ and $\varphi\le B$ ($0<a\le b$, $B>0$), $R\ge0$, $\varepsilon>0$. Then there are $0<c\le1$, $\kappa>0$, $K\ge0$ such that for all sufficiently large $U$: for every $0\le r\le R$, `RowData`, finite `rows` with $N((u))\le U$, $W$ smooth with support in $[w_a,w_b]$ ($w_a>0$, $w_b\ge0$), $C,T\ge0$, $\sigma_u\in[0,1]$, $\mathrm{freq}_u\in[-T,T]$, if `RawMoment data (twistProfile (logTest W n) s t) c κ C` and the same for its `scaleProfile` hold for all $n\le2$, $s\in[0,1]$, $t\in[-T,T]$, then
--   $$\sum_{u\in\mathrm{rows}}\|\texttt{polynomial}(\mathrm{data.character}\,u)\,\mathrm{true}\,W\,U^r\,\sigma_u\,\mathrm{freq}_u\|^2\le12(1+T)\,C\,K\,U^{\texttt{sourceExponent}\,r+\varepsilon}.$$
--
--   Lean: `OAI.SevenEighths.HeckeInverseAmplification.no_slot_rowwise_endpoint` in `lean/OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationRowwise.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorRowwisePolynomial

theorem no_slot_rowwise_endpoint
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y, 0≤φ y) (hφne : φ≠0)
    (a b B : ℝ) (ha : 0<a) (hab : a≤b) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo a b) (hφB : ∀ y, φ y≤B)
    (R ε : ℝ) (hR : 0≤R) (hε : 0<ε) :
    ∃ c κ K : ℝ, 0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (r : ℝ) (data : RowData) (rows : Finset FreeRow) (W : ℝ→ℂ)
        (wa wb C T : ℝ) (σ freq : FreeRow→ℝ),
      0≤ r → r≤R → 0≤C → 0≤T →
      0<wa → 0≤wb → Function.support W⊆Icc wa wb → ContDiff ℝ ∞ W →
      (∀ u∈rows, ((Ideal.span {u.val}).absNorm : ℝ)≤U) →
      (∀ u∈rows, σ u∈Icc 0 1) → (∀ u∈rows, freq u∈Icc (-T) T) →
      (∀ n : ℕ, n≤2 → ∀ s∈Icc (0 : ℝ) 1, ∀ t∈Icc (-T) T,
        RawMoment data (twistProfile (logTest W n) s t) c κ C ∧
        RawMoment data (scaleProfile (twistProfile (logTest W n) s t)) c κ C) →
      (∑ u∈rows, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W (U^r) (σ u) (freq u)‖^2)≤
        12*(1+T)*(C*K*U^(sourceExponent r+ε)) := by
  sorry

end SevenEighths.HeckeInverseAmplification

end

end OAI
end
