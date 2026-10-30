-- Prove2me | Theorems.Thm_FoundationsRL_DECLower_tvDist_avgActionDist_le_tvDist_histLaw
-- name    : FoundationsRL.DECLower.tvDist_avgActionDist_le_tvDist_histLaw
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:19:14.284665+00:00
-- url     : https://prove2.me/theorems/a6a6fa55-07ab-470f-9e96-20f198aa3679
-- title:
--   Data processing for the average action distribution, $D_{\mathrm{TV}}(p_M,p_{M'})\le D_{\mathrm{TV}}(\mathbb P^M,\mathbb P^{M'})$
-- statement:
--   Let $p$ be an algorithm and $M,M':\Pi\to\Delta(\mathbb R\times\mathcal O)$ probability kernels. For every horizon $T$,
--
--   $$
--   D_{\mathrm{TV}}\bigl(p_M,p_{M'}\bigr)\le D_{\mathrm{TV}}\bigl(\mathbb P^M,\mathbb P^{M'}\bigr),
--   $$
--
--   where $p_M$, $p_{M'}$ are the average action distributions and $\mathbb P^M$, $\mathbb P^{M'}$ the laws of the history $H_T$.
--
--   The average action distribution is the image of the history law under one fixed Markov kernel (the average of the algorithm's decision distributions), so the data-processing inequality applies. It transfers indistinguishability of the two histories to the decisions the algorithm plays.
--
--   Differences from the source:
--   - reading: "$D_{\mathrm{TV}}(p_M,p_{\widehat M})\le D_{\mathrm{TV}}(\mathbb P^M,\mathbb P^{\widehat M})\le 1/10$ by the data-processing inequality and (6.39)" → the first link only; reason: the second link is (6.39), which holds only for the specific pair of models and radius of the notes' simplified proof under assumption (6.34); the data-processing link is the general fact
--   - generalization: $M,\widehat M$ models of the class → any probability kernels, and every $T\in\mathbb N$; reason: the data-processing inequality uses neither the reward range nor $T\ge1$ (at $T=0$ both average action distributions are zero); models with $T\ge1$ are a special case
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, proof of Proposition 28, Step 1, p. 109 (after (6.42))

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_tvDist
import Definitions.Def_FoundationsRL_DECLower_avgActionDist

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.DECLower

/-- **Data processing for the average action distribution (p. 109).**
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, proof of Proposition 28, p. 109: "since D_TV(p_M, p_M̂) ≤ D_TV(P^M, P^M̂) ≤ 1/10 by the
data-processing inequality and (6.39)."

For every algorithm, Markov kernels `M, M'` and every `T`:
`D_TV(p_M, p_{M'}) ≤ D_TV(P^M, P^{M'})`.

**Formalization Note.** Only the data-processing step is stated; the further `≤ 1/10` is (6.39) of
the notes' simplified proof (it needs the simplifying assumption (6.34)). `T = 0` is allowed (both
average action distributions are the zero measure). -/
theorem tvDist_avgActionDist_le_tvDist_histLaw {D O : Type*} [MeasurableSpace D]
    [MeasurableSpace O] (alg : Algorithm D O) (M M' : Kernel D (ℝ × O))
    [IsMarkovKernel M] [IsMarkovKernel M'] (T : ℕ) :
    tvDist (avgActionDist alg M T) (avgActionDist alg M' T)
      ≤ tvDist (histLaw alg M T) (histLaw alg M' T) := by sorry

end FoundationsRL.DECLower
