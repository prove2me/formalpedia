-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeFinalAssembly_adaptive_source_count_from_raw_moments
-- name    : OAI.SevenEighths.ProbeFinalAssembly.adaptive_source_count_from_raw_moments
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:27:58.654001+00:00
-- url     : https://prove2.me/theorems/304d397c-c92d-4c82-8949-f8d7a20284a9
-- title:
--   Adaptive row count of a batch, final assembly form
-- statement:
--   The final-assembly version of `ProbeHighRowFamily.adaptive_source_count_from_raw_moments`, with the moment constants taken from a `counts` record (`counts.cB`, `counts.kB`, `counts.cH`, `counts.kH`): under the same hypotheses, eventually in $Z$, the number of rows of a batch is at most $K\,C\,Z^{\mathrm{logCost}+\mathrm{heightCost}+\mathrm{momentCost}}(Z^d)^{\texttt{adaptiveRowExponent}(2a-1,q,\Delta,\varepsilon,\varepsilon_m,B.\mathrm{mesh},\nu)}$.
--
--   Lean: `OAI.SevenEighths.ProbeFinalAssembly.adaptive_source_count_from_raw_moments` in `lean/OAI/NumberTheory/DirichletL/Detector/FinalAssemblySourceCount.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff
open ProbeHighRowFamily

theorem adaptive_source_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm)
    (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0<dmin) (hdmax : 0<dmax) (hτ : 0<τ)
    (hl : 0<logCost) (hh : τ<heightCost) (hb : 0<binWidth) (counts : CountParameters M H εm) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀(a ε Δ ν C q : ℝ) (i : ℕ),i≤n → 51/100<a → a≤1 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤C →
      ∀{Slot : Type} (B : Batch M H Label Slot (Z^d) a ε
        (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH) (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤K*C*Z^(logCost+heightCost+momentCost)*(Z^d)^(adaptiveRowExponent (2*a-1) q Δ ε εm B.mesh ν) := by
  sorry

end SevenEighths.ProbeFinalAssembly

end

end OAI
end
