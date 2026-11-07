-- Prove2me | Theorems.Thm_HardCoreBochner_comparison_display
-- name    : HardCoreBochner.comparison_display
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:32:37.432517+00:00
-- url     : https://prove2.me/theorems/9780f1cc-bae7-4179-af02-50311072ce4f
-- title:
--   Comparison display — $\langle f,(I-P_{GD})f\rangle_\mu\ge\langle f,-Lf\rangle_\mu/((1+r_{\max})|V|)$
-- statement:
--   Let $\mu$ be a distribution fully supported on a non-empty downward-closed family $X\subseteq\{0,1\}^V$, $V$ non-empty, with Glauber dynamics $P_{GD}$ defined as in (1). For every $f:\{0,1\}^V\to\mathbb R$,
--   $$\langle f,(I-P_{GD})f\rangle_\mu=\frac1{|V|}\sum_{v\in V}\mathbb E_\mu\Big[\frac{r_v(\sigma)}{1+r_v(\sigma)}\big(D^+_vf(\sigma)\big)^2\Big]\ \ge\ \frac{\sum_{v\in V}\mathbb E_\mu\big[r_v(\sigma)(D^+_vf(\sigma))^2\big]}{(1+r_{\max})|V|}=\frac{\langle f,-Lf\rangle_\mu}{(1+r_{\max})|V|},$$
--   where $r_{\max}=\max_{\sigma\in X,v\in V}r_v(\sigma)$. All three relations (the equality, the inequality and the last equality) are stated.
--
--   This is the standard comparison of Dirichlet forms between continuous-time and discrete-time Glauber dynamics.
--
--   Differences from the source:
--   - encoding: a distribution µ fully supported on a non-empty downward-closed family X ⊆ {0,1}^V → IsDownClosedLaw µ for µ : (V → Bool) → ℝ, with X := {σ | 0 < µ σ}; reason: the support of such a µ is exactly such an X, and every such pair (X, µ) arises this way; same instances
--   - encoding: P_GD, the Glauber dynamics for µ defined as in (1) → MarkovMixing.glauber µ (published heat-bath matrix) on all of V → Bool; reason: off the diagonal it is (1); its rows outside X carry weight µ(σ) = 0 in every µ-weighted form
--   - encoding: the factor 1/|V| for the vertex set V of the chain → [Nonempty V]; reason: excludes only V = ∅, where 1/|V| is undefined (Lean's 1/0 = 0 would make the identity false)
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), comparison display, p.3 (PDF p.3)

import Definitions.Def_mm_mcmc
import Definitions.Def_HardCoreBochner_IsDownClosedLaw
import Definitions.Def_HardCoreBochner_gen
import Definitions.Def_HardCoreBochner_ip
import Definitions.Def_HardCoreBochner_dirP
import Definitions.Def_HardCoreBochner_rmax

namespace HardCoreBochner

open scoped BigOperators

/-- **Comparison of Dirichlet forms.** Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), comparison display, p.3: for every `f`,
`⟨f, (I − P_GD)f⟩_µ = (1/|V|) Σ_v E_µ[ r_v(σ)/(1 + r_v(σ)) (D⁺_v f(σ))² ]
  ≥ Σ_v E_µ[ r_v(σ)(D⁺_v f(σ))² ] / ((1 + r_max)|V|) = ⟨f, −Lf⟩_µ / ((1 + r_max)|V|)`,
where `r_max = max_{σ∈X, v∈V} r_v(σ)` and the last equality is Lemma 2.1.

**Formalization Note** `P_GD` is the published heat-bath matrix `MarkovMixing.glauber µ` on all of
`{0,1}^V` ("we may define the Glauber dynamics for µ exactly as we did for the hard-core model in
(1)", p.3); its rows outside `X` carry weight `µ σ = 0`. `[Nonempty V]`: on an empty `V` the
factor `1/|V|` is `0` in Lean and the first equality fails. -/
theorem comparison_display {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (μ : (V → Bool) → ℝ) (hμ : IsDownClosedLaw μ) (f : (V → Bool) → ℝ) :
    dirP μ (MarkovMixing.glauber μ) f =
        (1 / (Fintype.card V : ℝ)) *
          ∑ v, expect μ (fun σ => rate μ v σ / (1 + rate μ v σ) * Dplus v f σ ^ 2) ∧
      (∑ v, expect μ (fun σ => rate μ v σ * Dplus v f σ ^ 2)) /
          ((1 + rmax μ) * Fintype.card V) ≤
        (1 / (Fintype.card V : ℝ)) *
          ∑ v, expect μ (fun σ => rate μ v σ / (1 + rate μ v σ) * Dplus v f σ ^ 2) ∧
      (∑ v, expect μ (fun σ => rate μ v σ * Dplus v f σ ^ 2)) /
          ((1 + rmax μ) * Fintype.card V) =
        ip μ f (fun σ => -gen μ f σ) / ((1 + rmax μ) * Fintype.card V) := by sorry

end HardCoreBochner
