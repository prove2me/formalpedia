-- Prove2me | Theorems.Thm_MaoLowDegree_Counterexample_lemma_3_4
-- name    : MaoLowDegree.Counterexample.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:43.196862+00:00
-- url     : https://prove2.me/theorems/da4d825a-ebc0-4648-a5b4-5258209bfbfb
-- title:
--   Lemma 3.4 — rank deficit under the noisy planted law
-- statement:
--   Fix the numerical construction parameters and any fixed valid constructed family $P_n$ of Section 2. Let $a,\sigma>0$ be rational and fix $\varepsilon\in[0,1)$. Define $\lambda=-\log_2(1-\varepsilon)$ and $\mu_n=N_0(1-\varepsilon)^T$, where $T=\lfloor a\ell_n\rfloor$ and $N_0=\lfloor\sqrt n\rfloor$. If $r\sigma/b<1/2$ and $bh_2(r\sigma/b)<1/2-a\lambda$, then
--   $$\Pr_{Y\sim T_\varepsilon P_n}\{N_0-\operatorname{rank}_{\mathbb F_2}M_s(Y)\ge\mu_n/2\}\longrightarrow1.$$
--
--   The deficit is compared in the reals, retaining the source's noninteger threshold. This gives the Planted success limit at each fixed noise rate, including zero; complete resampling is excluded exactly as in the source.
--
--   Differences from the source:
--   - encoding: the fixed subspace, basis, points and planted family of Sections 2–3 → CodeData, Construction and ValidConstruction with explicit standing numerical hypotheses; reason: expands the section preamble without assuming a graph-law conclusion
--   - encoding: for all sufficiently large n and probability 1-o(1) → Filter.atTop eventual assertions and Tendsto to 1; reason: these are the literal asymptotic quantifiers, with all fixed parameters before n
--   - encoding: N0 minus binary matrix rank compared to mu_n/2 → real coercions before subtraction; reason: avoids natural-number truncation of the source inequality
-- source:
--   Songtao Mao, STOC 2027 submission #509 (October 2026), Lemma 3.4, p.13; construction, pp.8–10

import Definitions.Def_MaoLowDegree_Counterexample_computationalClaims

open Classical Filter
open scoped Topology
noncomputable section
set_option autoImplicit false

namespace MaoLowDegree.Counterexample

/-- Lemma 3.4, p.13. The deficit subtraction is in ℝ, not truncated ℕ arithmetic. -/
theorem lemma_3_4 (r : ℕ) (β₁ β₂ b κ : ℝ)
    (hparams : Admissible r β₁ β₂ b κ) (C : Construction r b κ)
    (hC : ValidConstruction β₁ C) (a σ : ℚ) (ha : 0 < a) (hσ : 0 < σ)
    (ε : Rate) (hε : ε.val < 1) (hrank : PlantedConditions r b a σ ε) :
    Tendsto (fun n => prob (noise ε (constructedFamily C n))
      (fun Y => cleanMean a ε n / 2 ≤ (columns n : ℝ) - (liftedRank a σ Y : ℝ)))
      atTop (nhds 1) := by sorry

end MaoLowDegree.Counterexample
