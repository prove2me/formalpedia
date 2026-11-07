-- Prove2me | Theorems.Thm_HardCoreBochner_eq_4
-- name    : HardCoreBochner.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:32:28.741028+00:00
-- url     : https://prove2.me/theorems/9bb757e1-670a-411d-888e-105150126546
-- title:
--   (4) — $\gamma(P_{GD}-I)\ge\gamma(L)/((1+r_{\max})|V|)$
-- statement:
--   Let $\mu$ be a distribution fully supported on a non-empty downward-closed family $X\subseteq\{0,1\}^V$, $V$ non-empty, with Glauber dynamics $P_{GD}$. The spectral gaps satisfy
--   $$\gamma(P_{GD}-I)\ \ge\ \frac{1}{(1+r_{\max})|V|}\,\gamma(L).\tag{4}$$
--   In inequality form: for every real $\gamma$, if $\gamma\,\mathrm{Var}_\mu(f)\le\langle f,-Lf\rangle_\mu$ for all $f$, then
--   $$\frac{\gamma}{(1+r_{\max})|V|}\,\mathrm{Var}_\mu(f)\le\langle f,(I-P_{GD})f\rangle_\mu\quad\text{for all } f.$$
--   It transfers the continuous-time gap of Theorem 1.2 to the discrete-time chain.
--
--   Differences from the source:
--   - encoding: a distribution µ fully supported on a non-empty downward-closed family X ⊆ {0,1}^V → IsDownClosedLaw µ for µ : (V → Bool) → ℝ, with X := {σ | 0 < µ σ}; reason: the support of such a µ is exactly such an X, and every such pair (X, µ) arises this way; same instances
--   - encoding: P_GD, the Glauber dynamics for µ defined as in (1) → MarkovMixing.glauber µ (published heat-bath matrix) on all of V → Bool; reason: off the diagonal it is (1); its rows outside X carry weight µ(σ) = 0 in every µ-weighted form
--   - encoding: the factor 1/|V| for the vertex set V of the chain → [Nonempty V]; reason: excludes only V = ∅, where 1/|V| is undefined (Lean's 1/0 = 0 would make the identity false)
--   - encoding: γ(P_GD − I) ≥ γ(L)/((1 + r_max)|V|), with γ(·) the infimum (2) → ∀ γ, (∀ f, γ Var_µ(f) ≤ ⟨f, −Lf⟩_µ) → ∀ f, γ/((1 + r_max)|V|) Var_µ(f) ≤ ⟨f, (I − P_GD)f⟩_µ; reason: a bound between two infima of ratios is equivalent to the implication between their inequality forms for every γ
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), (4), p.3 (PDF p.3)

import Definitions.Def_mm_mcmc
import Definitions.Def_HardCoreBochner_IsDownClosedLaw
import Definitions.Def_HardCoreBochner_gen
import Definitions.Def_HardCoreBochner_ip
import Definitions.Def_HardCoreBochner_dirP
import Definitions.Def_HardCoreBochner_rmax

namespace HardCoreBochner

open scoped BigOperators

/-- **Equation (4).** Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), (4), p.3: "It follows from (2) that γ(PGD − I) ≥ (1/((1 + rmax)|V|)) γ(L)."

In Poincaré form: if `γ Var_µ(f) ≤ ⟨f, −Lf⟩_µ` for all `f`, then
`γ/((1 + r_max)|V|) · Var_µ(f) ≤ ⟨f, (I − P_GD)f⟩_µ` for all `f`.

**Formalization Note** `P_GD` is `MarkovMixing.glauber µ` (see `comparison_display`); `[Nonempty V]`
for the factor `1/|V|`. The spectral gaps are written as the Poincaré inequalities they mean. `γ` is
any real number (for `γ ≤ 0` both sides are trivial). -/
theorem eq_4 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (μ : (V → Bool) → ℝ) (hμ : IsDownClosedLaw μ) (γ : ℝ)
    (hgap : ∀ f : (V → Bool) → ℝ, γ * var μ f ≤ ip μ f (fun σ => -gen μ f σ))
    (f : (V → Bool) → ℝ) :
    γ / ((1 + rmax μ) * Fintype.card V) * var μ f ≤ dirP μ (MarkovMixing.glauber μ) f := by sorry

end HardCoreBochner
