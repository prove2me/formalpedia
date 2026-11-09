-- Prove2me | Theorems.Thm_MaoLowDegree_Counterexample_lemma_3_3
-- name    : MaoLowDegree.Counterexample.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:49.652534+00:00
-- url     : https://prove2.me/theorems/51861340-73c0-410d-ace2-551ea5e75d84
-- title:
--   Lemma 3.3 — full rank under the null
-- statement:
--   Let $\gamma_0>0$ have the puncturing property of Lemma 3.1. Fix positive rational constants $a,\sigma$ such that $a>2$, $\sigma/a<\min\{\gamma_0,1/2\}$ and $ah_2(\sigma/a)>1/2$. For $Y\sim Q_n$, with $T=\lfloor a\ell_n\rfloor$, $s=\lfloor\sigma\ell_n\rfloor$ and $N_0=\lfloor\sqrt n\rfloor$, the lifted anchor matrix satisfies
--   $$\Pr\{\operatorname{rank}_{\mathbb F_2}M_s(Y)=N_0\}\longrightarrow1.$$
--
--   This supplies the Null success limit for Algorithm 1. The finite cases with invalid anchor/column ranges have a total adjacency convention and do not affect the limit.
--
--   Differences from the source:
--   - encoding: vertices 1 through n and unordered edges → Fin n with increasing endpoint pairs; n=0 is an empty-cube extension; reason: relabeling by subtracting one changes no positive-n instance
--   - encoding: for all sufficiently large n and probability 1-o(1) → Filter.atTop eventual assertions and Tendsto to 1; reason: these are the literal asymptotic quantifiers, with all fixed parameters before n
--   - encoding: the fixed gamma0 from Lemma 3.1 → positive gamma0 with the full Puncturing property; reason: makes the cited constant and its standing property explicit
-- source:
--   Songtao Mao, STOC 2027 submission #509 (October 2026), Lemma 3.3, p.12; §3.1, pp.11–12

import Definitions.Def_MaoLowDegree_Counterexample_computationalClaims

open Classical Filter
open scoped Topology
noncomputable section
set_option autoImplicit false

namespace MaoLowDegree.Counterexample

/-- Lemma 3.3, p.12. Full F₂ column rank under the null, as a probability limit. -/
theorem lemma_3_3 (γ₀ : ℝ) (hγ : 0 < γ₀) (hpunct : Puncturing γ₀)
    (a σ : ℚ) (hparams : NullConditions γ₀ a σ) :
    Tendsto (fun n => prob (nullLaw n) (fun Y => liftedRank a σ Y = columns n))
      atTop (nhds 1) := by sorry

end MaoLowDegree.Counterexample
