-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_InfiniteGeneration_orbit_local_approximation
-- name    : OAI.FreeGroupFactorMain.InfiniteGeneration.orbit_local_approximation
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T02:55:47.360307+00:00
-- url     : https://prove2.me/theorems/1b127cc8-7c58-4e3a-94f8-815bb1d3c385
-- title:
--   Local approximation inside the orbit at infinite rank
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $\mathrm{Index}=\mathrm{Fin}\,3\sqcup\mathbb N\sqcup\{*\}$ and $M=L(\mathbb F(\mathrm{Index}))$. Let $A_i=\lambda(i)$ for $i\in\mathrm{Fin}\,3$ be the initial tuple, and for $q\in\mathbb N\sqcup\{*\}$ let $E_q=\lambda(q)$ be the extra generators. The orbit is the set of tuples $(\Phi(A_i))_i$ for $\tau$-preserving $*$-automorphisms $\Phi$ of $M$. Tuples carry the metric $\mathrm{dist}(V,U)=\max_i\|V_i-U_i\|$ in the operator norm. Assume that for every $\tau$-preserving automorphism $\Phi$, finite $s\subset\mathrm{Index}$ and $\theta>0$ there are $V$ in the orbit with $\mathrm{dist}(V,\Phi(A))<\theta$ and words $w_j\in\mathbb F_3$ with $\|V_{w_j}-\Phi(\lambda(j))\|_2<\theta$ for all $j\in s$. Then for every $U$ in the orbit, $\delta,\varepsilon>0$ and $g\in\mathbb F(\mathrm{Index})$, there are $V$ in the orbit with $\mathrm{dist}(V,U)<\delta$ and a finitely supported $p:\mathbb F_3\to\mathbb C$ with
--
--   $$\Bigl\|\sum_hp(h)V_h-\lambda(g)\Bigr\|_2<\varepsilon.$$
--
--   This reduces density at infinite rank to finitely many generators at a time.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.InfiniteGeneration.orbit_local_approximation`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/InfiniteGeneration.lean#L379

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

namespace FreeGroupFactorMain.Generation

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain.InfiniteGeneration
open Generation

end FreeGroupFactorMain.InfiniteGeneration

namespace FreeGroupFactorMain.Generation
variable {G : Type uG} [Group G] {ι : Type uι}

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain.InfiniteGeneration
open Generation

theorem orbit_local_approximation
    (hstep : ∀ (Φ : M ≃⋆ₐ[ℂ] M), (∀ T, canonicalTrace (Φ T) = canonicalTrace T) →
      ∀ (s : Finset Index) (θ : ℝ), 0 < θ →
        ∃ V ∈ orbit, dist V (mapTuple Φ initial) < θ ∧
          ∃ w : Index → FreeGroup (Fin 3), ∀ j ∈ s,
            twoNorm ((wordTuple V w j : M)-(mapTuple Φ generatorUnitary j : M)) < θ)
    (U : Tuple) (hU : U ∈ orbit) (δ : ℝ) (hδ : 0 < δ)
    (g : Group) (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ orbit, dist V U < δ ∧ ∃ p : FreeGroup (Fin 3) →₀ ℂ,
      dist (groupL2 (poly V p)) (lp.single 2 g (1 : ℂ)) < ε := by
  sorry

end FreeGroupFactorMain.InfiniteGeneration
end
end OAI
