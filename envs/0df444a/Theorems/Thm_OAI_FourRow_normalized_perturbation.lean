-- Prove2me | Theorems.Thm_OAI_FourRow_normalized_perturbation
-- name    : OAI.FourRow.normalized_perturbation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T17:53:00.964119+00:00
-- url     : https://prove2.me/theorems/313dcbbd-1a53-49df-a22e-82d3f4565aa7
-- title:
--   Total variation perturbation bound for permanent expectations under laws on $S_4$ with uniform marginals
-- statement:
--   Let $S_4$ be the group of permutations of the sites $\{0,1,2,3\}$, and let $\nu:S_4\to\mathbb{R}$ be a probability law ($\nu(\pi)\ge0$ for all $\pi$ and $\sum_\pi\nu(\pi)=1$) with uniform marginals, i.e. $\sum_{\pi:\,\pi(i)=j}\nu(\pi)=\tfrac14$ for all sites $i,j$. Let $u(\pi)=\tfrac1{24}$ be the uniform law and $d_{\mathrm{TV}}(\nu,u)=\tfrac12\sum_{\pi\in S_4}\bigl|\nu(\pi)-\tfrac1{24}\bigr|$ the total variation distance between them. For a law $\mu$ on $S_4$ and a real $4\times4$ array $f=(f_{ij})$ put $\mathbb{E}_\mu[f]=\sum_{\pi\in S_4}\mu(\pi)\prod_{i=0}^{3}f_{i\pi(i)}$. If $f$ has nonnegative entries and rows normalized by $\sum_{j=0}^{3}f_{ij}^2=4$ for each $i$, and $\Delta(f)=\sum_{i,j=0}^{3}(f_{ij}-1)^2$, then
--   $$
--   \mathbb{E}_\nu[f]\le\mathbb{E}_u[f]+6\,d_{\mathrm{TV}}(\nu,u)\,\Delta(f).
--   $$
--
--   No smallness assumption on $d_{\mathrm{TV}}(\nu,u)$ is needed. The error term is of second order in the deviation of $f$ from the all-ones matrix $J$, reflecting the fact that $\nu$ and $u$ have the same one-site marginals. Combined with the exponent-two stability bound for the uniform law, this transfers the permanent inequality to all laws with uniform marginals that are close to uniform in total variation.
--
--   **Formalization Note** Here $\mathbb{E}_\mu[f]$ is `permanentExpectation μ f`, $u$ is `uniformLaw`, $d_{\mathrm{TV}}(\nu,u)$ is `totalVariation ν` (defined directly as half the sum of the deviations from $1/24$), the hypotheses on $\nu$ are `IsProbability ν` and `UniformMarginals ν`, and $\Delta(f)$ is `totalDist f`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Permanent/Perturbation.lean#L79-L119

import Mathlib
import Definitions.Def_FourRowPermanent
import Definitions.Def_OAI_Combinatorics_Permanent_Stability

open OAI OAI.FourRow
open scoped BigOperators

theorem OAI.FourRow.normalized_perturbation (ν : Law) (hp : IsProbability ν)
    (hm : UniformMarginals ν) (f : Functions) (hf : ∀ i j, 0 ≤ f i j)
    (hn : ∀ i, rowSq (f i) = 4) :
    permanentExpectation ν f ≤ permanentExpectation uniformLaw f +
      6 * totalVariation ν * totalDist f := by sorry
