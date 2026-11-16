-- Prove2me | Theorems.Thm_KMPMixing_Supplement_theorem_5_5
-- name    : KMPMixing.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:55:53.131302+00:00
-- url     : https://prove2.me/theorems/a84ab5e3-0445-49d3-b16e-b809970c988d
-- title:
--   Theorem 5.5 — the continuous KMP chain mixes in $O(\gamma^{-1}(\log d+\log(1/\varepsilon)))$ steps
-- statement:
--   Let $G=([d],E)$ be a connected graph on $d\ge2$ vertices, $K^{(G)}$ the transition kernel of the continuous KMP chain on $\Delta^{\mathrm{cont}}_G=\{v\in\mathbb R^d_{\ge0}:\sum_xv_x=1\}$, and $\mu_G=\mathrm{Dirichlet}(1,\dots,1)$ its uniform stationary distribution. Let $\gamma^{(1,G)}_{\mathrm{KMP}}$ be the spectral gap of the single-particle KMP chain on $G$.
--
--   There is an absolute constant $C>0$ such that, for every such $G$ and every $\varepsilon\in(0,1)$, the total-variation mixing time is at most
--   $$
--   \frac{C}{\gamma^{(1,G)}_{\mathrm{KMP}}}\Big(\log d+\log\frac1\varepsilon\Big),
--   $$
--   that is, some $k\in\mathbb N$ below this bound satisfies
--   $$
--   \sup_{v\in\Delta^{\mathrm{cont}}_G}\big\|(K^{(G)})^k(v,\cdot)-\mu_G\big\|_{\mathrm{TV}}\le\varepsilon.
--   $$
--
--   The bound has no dependence on a particle number: it is the continuum counterpart of the mission's goal, and it yields Corollary 5.6.
--
--   **Formalization Note** $C$ is quantified before $d$, $G$ and $\varepsilon$. $\gamma^{(1,G)}_{\mathrm{KMP}}$ is `MarkovMixing.absSpectralGap (kmpChain G 1)`, as in the mission's goal. $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: the total-variation mixing time is at most B → some k ∈ ℕ with k ≤ B has sup over v ∈ Δ^cont_G of ‖K^k(v,·) − µ_G‖_TV ≤ ε; reason: the mixing time is the least such k, so the two statements are equivalent; this avoids an sInf junk value
--   - encoding: spectral gap γ^{(1,G)}_KMP of the single-particle chain → MarkovMixing.absSpectralGap (kmpChain G 1); reason: the published goal's convention; the single-particle chain is lazy, so its absolute and plain gaps coincide
--   - encoding: transition kernel K^{(G)} on Δ^cont_G and µ_G = Dirichlet(1,…,1) → a Markov kernel on ℝ^d started inside contSimplex d, and PolyVoting.dirichletMeasure (fun _ => 1) on ℝ^d; reason: the simplex is invariant under the kernel, and the Dirichlet measure is concentrated on it; the same laws
-- source:
--   Chen, Liu, Qin, Schulman, Song, Yao, Zhao, A Tale of Two Walks: From Kac to KMP and Back, arXiv:2609.38044 (sha256 6a9abdd4…), Theorem 5.5, p.35 (PDF p.37); Definition 5.1, pp.32–33; proof pp.36–38

import Mathlib
import Definitions.Def_KMPMixing_kmpChain
import Definitions.Def_PolyVoting_dirichletMeasure
import Definitions.Def_KMPMixing_Supplement_contKMP

namespace KMPMixing.Supplement

open MarkovMixing KMPMixing

/-- **Theorem 5.5** (Chen, Liu, Qin, Schulman, Song, Yao, Zhao, *A Tale of Two Walks: From Kac to
KMP and Back*, arXiv:2609.38044, p.35 (PDF p.37)). There is an absolute constant `C > 0` such
that for every connected graph `G = ([d], E)` on `d ≥ 2` vertices and every `ε ∈ (0, 1)`, the
total-variation mixing time of the continuous KMP chain `K^{(G)}` to its uniform stationary law
`µ_G = Dirichlet(1, …, 1)` is at most `(C / γ^{(1,G)}_KMP) · (log d + log(1/ε))`, where
`γ^{(1,G)}_KMP` is the spectral gap of the single-particle KMP chain on `G`.

**Formalization Note** "Mixing time at most `B`" is stated as: some `k ∈ ℕ` with `k ≤ B` has
`sup_{v ∈ Δ^cont_G} ‖K^k(v, ·) − µ_G‖_TV ≤ ε` (the least such `k`, the mixing time, is then
`≤ B`). `C` is quantified before `d`, `G` and `ε`. `γ^{(1,G)}_KMP` is
`MarkovMixing.absSpectralGap (kmpChain G 1)`, as in the mission's goal (the single-particle
chain is lazy, so this is its spectral gap). `µ_G` is `PolyVoting.dirichletMeasure (fun _ => 1)`
on `ℝ^d`. `log` is the natural logarithm. -/
theorem theorem_5_5 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 2 ≤ d →
      ∀ (G : SimpleGraph (Fin d)) [DecidableRel G.Adj], G.Connected →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ k : ℕ, (k : ℝ) ≤ C / absSpectralGap (kmpChain G 1) * (Real.log d + Real.log (1 / ε)) ∧
          ∀ v ∈ contSimplex d,
            tvMeasure (kernelLaw (contKMPKernel G) k v)
              (PolyVoting.dirichletMeasure (fun _ : Fin d => (1 : ℝ))) ≤ ε := by sorry

end KMPMixing.Supplement
