-- Prove2me | Theorems.Thm_McFadden1974_RandomUtility_lemma1_integrand
-- name    : McFadden1974.RandomUtility.lemma1_integrand
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:43:52.181572+00:00
-- url     : https://prove2.me/theorems/dc2116b3-08cc-412b-acf4-3e226e0bb996
-- title:
--   Lemma 1, proof — the integrand of (3) under the extreme value law
-- statement:
--   For real $\varepsilon$, representative utilities $V_1,\dots,V_J$ and an alternative $i$,
--   $$
--   \Big(e^{-\varepsilon} e^{-e^{-\varepsilon}}\Big) \prod_{j \ne i} \exp\!\big(-e^{-(\varepsilon + V_i - V_j)}\big)
--   = e^{-\varepsilon} \prod_{j=1}^{J} \exp\!\big(-e^{-\varepsilon - V_i + V_j}\big)
--   = e^{-\varepsilon} \exp\!\Big(-e^{-\varepsilon} \sum_{j=1}^{J} e^{V_j - V_i}\Big).
--   $$
--
--   The left side is the integrand $F_i(\varepsilon + V_i - V_1, \dots, \varepsilon + V_i - V_J)$ of Equation (3) when the shocks are i.i.d. with the extreme value law (13): the density $e^{-\varepsilon}e^{-e^{-\varepsilon}}$ of (13) at $\varepsilon$ times the distribution functions of the other $J-1$ shocks. The right side is the closed form that, substituted into (3), gives the logit formula (12) in Lemma 1.
--
--   **Formalization Note** The paper's product runs over all $j = 1,\dots,J$; its factor for $j = i$ is $e^{-e^{-\varepsilon}}$, the second factor of the density, which is why the left side writes the density out and multiplies over $j \ne i$.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 111, Lemma 1, proof (PDF p. 7)

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model

open MeasureTheory ProbabilityTheory Finset

namespace McFadden1974.RandomUtility

/-- **Lemma 1, proof — the integrand of (3) under (13)** (McFadden, Conditional Logit Analysis of
Qualitative Choice Behavior, in Frontiers in Econometrics (1974), p. 111, Lemma 1, proof;
PDF p. 7): "From Equation (13), letting `V_i = v(s, x_i)`,
`F_i(ε + V_i − V_1, …, ε + V_i − V_J) = exp(−ε) ∏_{j=1}^{J} exp(−exp(−ε − V_i + V_j))
= exp(−ε) exp⟨−[exp(−ε)][Σ_{j=1}^{J} exp(V_j − V_i)]⟩`."

The left side is `F_i` for i.i.d. shocks with law (13): the density
`exp(−ε) exp(−exp(−ε))` of (13) at `ε`, times the distribution functions
`exp(−exp(−(ε + V_i − V_j)))` of the other `J − 1` shocks.

Formalization Note: the paper's product runs over all `j = 1, …, J`; its factor `j = i`,
`exp(−exp(−ε))`, is the second factor of the density. The statement gives both equalities of
the display, with the product over `j ≠ i` and the density written out on the left. -/
theorem lemma1_integrand {J : ℕ} (V : Fin J → ℝ) (i : Fin J) (ε : ℝ) :
    (Real.exp (-ε) * Real.exp (-Real.exp (-ε))) *
        ∏ j ∈ univ.erase i, Real.exp (-Real.exp (-(ε + V i - V j)))
      = Real.exp (-ε) * ∏ j, Real.exp (-Real.exp (-ε - V i + V j)) ∧
    Real.exp (-ε) * ∏ j, Real.exp (-Real.exp (-ε - V i + V j))
      = Real.exp (-ε) * Real.exp (-(Real.exp (-ε)) * ∑ j, Real.exp (V j - V i)) := by sorry

end McFadden1974.RandomUtility
