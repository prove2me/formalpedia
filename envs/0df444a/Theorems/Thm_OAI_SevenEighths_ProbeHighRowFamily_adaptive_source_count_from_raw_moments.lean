-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_adaptive_source_count_from_raw_moments
-- name    : OAI.SevenEighths.ProbeHighRowFamily.adaptive_source_count_from_raw_moments
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:18:52.968204+00:00
-- url     : https://prove2.me/theorems/7887c76c-cbf2-4636-ae06-9dd9edda276f
-- title:
--   Adaptive row count of a batch from raw fiber moments
-- statement:
--   Let $M\ne0$, $H\supseteq$`globalUnits M`, $S$ finite, $\varphi$ smooth, compactly supported in $(a_0,b_0)\subseteq(0,\infty)$, nonnegative, nonzero, bounded by $B_0>0$, $\varepsilon_m>0$, a finite label type, $N,n\in\mathbb N$, and reals $d_{\min},d_{\max},\tau,\mathrm{logCost},\mathrm{binWidth}>0$, $\mathrm{heightCost}>\tau$, `momentCost`. Then there are $0<c_B,c_H\le1$, $\kappa_B,\kappa_H>0$, $K>0$ such that for all sufficiently large $Z$: for every $d\in[d_{\min},d_{\max}]$, reals $a\in(51/100,1]$, $0\le\varepsilon\le1/1000$, $0\le\Delta\le1/8$, $\nu>0$, $C\ge0$, $q$, $i\le n$, and every nonempty `Batch` $B$ (at $U=Z^d$, cutoff `cutoff (2a-1) q`, $T=Z^\tau$, allowance $(Z^d)^{\tau/(2d_{\max})}$) with at most $N$ slots, bin width `binWidth`, all rows of `rowMean` $q$, and `Moments` of every nonempty fiber with constants $(c,\kappa)=(c_B,\kappa_B)$ if $2a-1\le5/6$ and $(c_H,\kappa_H)$ otherwise, $C\,Z^{\mathrm{momentCost}}$ and height $Z^{\mathrm{heightCost}}$: the number of rows of $B$ is at most $K\,C\,Z^{\mathrm{logCost}+\mathrm{heightCost}+\mathrm{momentCost}}(Z^d)^{\texttt{adaptiveRowExponent}(2a-1,q,\Delta,\varepsilon,\varepsilon_m,B.\mathrm{mesh},\nu)}$.
--
--   Lean: `OAI.SevenEighths.ProbeHighRowFamily.adaptive_source_count_from_raw_moments` in `lean/OAI/NumberTheory/DirichletL/PrimeRows/NonfloorSourceCount.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff

theorem adaptive_source_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm)
    (Label : Type*) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0<dmin) (hdmax : 0<dmax) (hτ : 0<τ)
    (hl : 0<logCost) (hh : τ<heightCost) (hb : 0<binWidth) :
    ∃cB κB cH κH K : ℝ,0<cB ∧ cB≤1 ∧ 0<κB ∧ 0<cH ∧ cH≤1 ∧ 0<κH ∧ 0<K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀(a ε Δ ν C q : ℝ) (i : ℕ),i≤n → 51/100<a → a≤1 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤C →
      ∀{Slot : Type*} (B : Batch M H Label Slot (Z^d) a ε
        (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ (if 2*a-1≤5/6 then cB else cH) (if 2*a-1≤5/6 then κB else κH) (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤K*C*Z^(logCost+heightCost+momentCost)*(Z^d)^(adaptiveRowExponent (2*a-1) q Δ ε εm B.mesh ν) := by
  sorry

end SevenEighths.ProbeHighRowFamily

end

end OAI
end
