-- Prove2me | Theorems.Thm_JuHardCoreTransition_Mixing_lemma_2_2
-- name    : JuHardCoreTransition.Mixing.lemma_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:17:39.698517+00:00
-- url     : https://prove2.me/theorems/c74d7bb5-4d31-49fd-aaf0-a08fc99439d4
-- title:
--   Lemma 2.2 — hard-core marginal response bound
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G=(V,E)$ have maximum degree at most $d\ge3$, and let $\mu=\mu_{G,\lambda}$ with $\lambda>0$ and $t=\log(\lambda/\lambda_c)\le\delta_{\mathrm{up}}=2^{-18}$. For every $0<h\le h_0=2^{-27}$, every field tilt $\psi\in[e^{-h},e^h]^V$ and every $v\in V$,
--   $$|(\psi*\mu)(X_v=1)-\mu(X_v=1)|\le C\lambda\big(\sqrt{t_+}+h^{1/3}\big),\qquad t_+=\max\{t,0\}.$$
--
--   Differences from the source:
--   - encoding: an n-vertex graph G=(V,E) → a SimpleGraph on Fin n (n labelled vertices); reason: every finite graph is isomorphic to one on Fin n and every quantity involved is isomorphism-invariant; this lets the absolute constant be stated before the graph
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), Lemma 2.2, printed p.9 / PDF p.10

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_HardCore
import Definitions.Def_JuHardCoreTransition_Mixing_BooleanLaws
import Definitions.Def_JuHardCoreTransition_Mixing_GlauberHardCore

namespace JuHardCoreTransition.Mixing

open HiddenHardCoreColoring.Mixing

/-- **Lemma 2.2 (Hard-core marginal response bound)** (printed p.9 / PDF p.10). There is an
absolute constant `C > 0` such that the following holds. Let `G` have maximum degree at most
`d ≥ 3`, and let `μ = μ_{G,λ}` with `λ > 0` and `t = log(λ/λ_c(d)) ≤ δ_up = 2^{−18}`. For every
`0 < h ≤ h₀ = 2^{−27}`, every field tilt `ψ ∈ [e^{−h}, e^h]^V` and every `v ∈ V`,
`|(ψ ∗ μ)(X_v = 1) − μ(X_v = 1)| ≤ Cλ(√t₊ + h^{1/3})`, `t₊ = max{t, 0}`.
(The vertex set of an `n`-vertex graph is `Fin n`.) -/
theorem lemma_2_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 3 ≤ d → ∀ n : ℕ, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v ≤ d) → ∀ lam : ℝ, 0 < lam → Real.log (lam / lamCrit d) ≤ deltaUp →
        ∀ h : ℝ, 0 < h → h ≤ hZero → ∀ ψ : Fin n → ℝ,
          (∀ v, Real.exp (-h) ≤ ψ v ∧ ψ v ≤ Real.exp h) → ∀ v : Fin n,
            |marg (tilt ψ (hcSetLaw G lam)) v - marg (hcSetLaw G lam) v| ≤
              C * lam * (Real.sqrt (max (Real.log (lam / lamCrit d)) 0) + h ^ (1 / 3 : ℝ)) := by sorry

end JuHardCoreTransition.Mixing
